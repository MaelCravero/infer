(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

(*
 * This schedulers aims at fixing the non-determinism induced by other schedulers which can be
 * explained by the following points:
 *
 * - Depending on the node of a cycle chosen as entry point we may have different analysis results.
 * - The entry point of a cycle chosen by the analysis is the first node of this cycle which gets
 *   processed by a given job.
 * - Execution time of jobs is not deterministic, hence the entry point of the cycle might vary
 *   drastically from one run to the next.
 *
 * Hence, to be deterministic we must ensure we always have the same entry point between runs. Based
 * on the fact that recursion cycles cannot occur between multiple strongly connected components,
 * this scheduler decomposes the callgraph into SCCs and schedules only one node (the "head") of
 * each SCC. All other nodes of the component are locked by default and can only be processed by the
 * job which is processing the head of their component. This means that the SCCs are always
 * processed by a single job, which removes parallelism-induced non-determinism.
 *
 * Since the components are scheduled in topological order with the leaves first (procedures with no
 * callees), it will always be able to make progress in at least one job, so when a job needs result
 * from a locked procedure (which is being processed elsewhere), it can simply wait until the result
 * becomes available. Contrary to the RestartScheduler, this means that the results of the analysis
 * of one job are not dropped if one dependency is not finished yet, so the overall CPU use is
 * reduced.
 *)

open! IStd
module L = Logging

(** Minimum size that a component must have to be simplified *)
let large_component_size = 300

(* Print the identity of the current process if it's a child *)
let pp_child fmt =
  match Config.run_as_child with None -> () | Some child -> Format.fprintf fmt "_%d" child


(* Retry reading and writing to files in cases of potential data races *)
let rec retry ?(times = 5) ?(delay = 0.02) f =
  try f ()
  with e ->
    L.(debug Analysis Quiet) "%a ; retrying@." Exn.pp e ;
    if times > 0 then
      ( ignore (Unix.nanosleep delay) ;
        retry ~times:(times - 1) )
        ~delay f
    else raise e


let write_all f ~data = retry (fun () -> Out_channel.write_all f ~data)

let read_all f = retry (fun () -> In_channel.read_all f)

(* Marshalling functions *)

let procname_locks_path = ResultsDir.get_path ProcnamesLocks

module type Data = sig
  val filename : string

  (** [t] must be serializable using Marshal *)
  type t
end

(** Functor to factorize code for storing/loading of data structures. *)
module MarshalledData (D : Data) = struct
  (* Each job needs to be aware of the composition of the components or their priorities in order to
     be able to know which procedures locks it can bypass to analyze a given component. We compute
     the maps in the parent process and marshal them to disk for the other jobs to access. *)

  let filename = procname_locks_path ^/ D.filename

  let store (map : D.t) =
    let oc = Out_channel.create ~binary:true filename in
    Marshal.to_channel oc map [] ;
    Out_channel.close oc


  let load () : D.t =
    let ic = In_channel.create ~binary:true filename in
    let res = Marshal.from_channel ic in
    In_channel.close ic ;
    res


  let data =
    (* Memoize value loading. *)
    let data = ref None in
    fun () ->
      match !data with
      | None ->
          let v = load () in
          data := Some v ;
          v
      | Some data ->
          data
end

(* Associate a component head to its other component members *)
module ComponentMap = struct
  include Caml.Hashtbl.Make (struct
    type t = Procname.t

    let equal lhs rhs = String.equal (Procname.to_unique_id lhs) (Procname.to_unique_id rhs)

    let hash pname = hash_string (Procname.to_unique_id pname)
  end)

  include MarshalledData (struct
    let filename = "component_map"

    type nonrec t = Procname.Set.t t
  end)
end

(* Associate each component head to its topological priority (lower is better) *)
module PriorityMap = struct
  include Procname.Map

  include MarshalledData (struct
    let filename = "priority_map"

    type nonrec t = int t
  end)
end

(* Edges of the callgraph *)
module Edge = struct
  (** Edge represented as a pair of (src, dst) *)
  type t = Procname.t * Procname.t

  let compare = Tuple2.compare ~cmp1:Procname.compare ~cmp2:Procname.compare
end

module EdgeSet = Caml.Set.Make (Edge)

(* Masked edges which should not be taken into account during analysis *)
module MaskedEdges = struct
  include EdgeSet

  include MarshalledData (struct
    let filename = "masked_edges"

    type nonrec t = t
  end)
end

let is_edge_masked edge =
  try EdgeSet.mem edge (MaskedEdges.data ())
  with _ -> false (* Edge map does not exist, edge cannot be masked. *)


(* Component priority and deadlock bypasses handling *)

let priority_prefix = "priority_pid_"

(** Each process has a priority, defined as the minimum priority of the procedures it currently
    analyzes. *)
module Priority = struct
  (** Priority is represented as a combination of the priority of the currently analyzed procedure
      as well as the minimum priority overall. This allows for efficient access to the minimum
      priority of all procedures analyzed, which corresponds to the priority of the process. *)
  type priority = {current: int; min: int}

  (** Priorities of the procedures being analyzed, following the analysis stack *)
  let priority_stack : priority Stack.t = Stack.create ()

  (** Get the priority of the current process *)
  let get () = match Stack.top priority_stack with Some {min} -> min | None -> Int.max_value

  (** Write the priority of the current process to disk *)
  let write () =
    let filename =
      procname_locks_path
      ^/ Format.asprintf "%s%a%t" priority_prefix Pid.pp (ProcessPoolState.get_pid ()) pp_child
    in
    let priority = get () in
    L.(debug Analysis Medium) "priority is %d@." priority ;
    write_all filename ~data:(Int.to_string priority)


  (** Register the start of the analysis of [pname] to the priority stack *)
  let push pname =
    L.(debug Analysis Medium) "starting analysis of %a@." Procname.pp pname ;
    let priorities = PriorityMap.data () in
    match Procname.Map.find_opt pname priorities with
    | None ->
        ()
    | Some rank ->
        Stack.push priority_stack {current= rank; min= Int.min rank (get ())} ;
        write ()


  (** Register the end of the analysis of [pname] to the priority stack *)
  let pop pname =
    let priorities = PriorityMap.data () in
    if Procname.Map.mem pname priorities then (
      L.(debug Analysis Medium) "finished analysis of %a@." Procname.pp pname ;
      ignore (Stack.pop_exn priority_stack : priority) ;
      write () )


  (** Get the minimum priority between *all* analysis processes *)
  let minimum () =
    let open Int in
    let min =
      Array.fold (Sys.readdir @@ procname_locks_path) ~init:max_value ~f:(fun acc f ->
          if not (String.is_prefix ~prefix:priority_prefix f) then acc
          else
            match procname_locks_path ^/ f |> read_all with
            | "" ->
                acc
            | text ->
                min acc (of_string text) )
    in
    if min <> max_value then min else -1
end

(* Locking functions *)

(*
 * At the start of the analysis, all elements of a strongly connected component are locked but one,
 * its "head". This forces the component head as the entry point to the component which fixes its
 * analysis order.
 *
 * When trying to lock a procedure, i.e. start analyzing it, we check if it is a component head. In
 * this case the process will have to be able to bypass the physical lock of the non-head elements
 * of the component. This is done through a concept of ownership: a given analysis jobs "owns" the
 * elements of the components it is analyzing, which means it will be able to skip locking them.
 * This simulates generating a physical lock (since one is already on disk). Once an already locked
 * procedure has been skipped, it is as if it were locked by the current process and can be worked
 * with just like any other procedure.
 *
 * To handle procedure calls which cannot be detected statically before the analysis, we attribute a
 * priority rank to each component based on the topological order. Each process is also attributed a
 * priority, defined as the minimum priority of all procedures it is currently analyzing. When all
 * processes are stalled and thus deadlocked, we allow the process with minimal rank to bypass locks
 * in order to make progress in its analysis. This solves deadlock by still remaining deterministic,
 * since the priority ranks are themselves attributed deterministically.
 *)

(* Use locks to communicate which processes are currently stopped. *)

let stalled_prefix = "stalled_pid_"

let procname_of_pid () =
  Procname.from_string_c_fun
    (Format.asprintf "%s%a%t" stalled_prefix Pid.pp (ProcessPoolState.get_pid ()) pp_child)


let mark_stalled, unmark_stalled =
  let stalled = ref false in
  let mark () =
    L.(debug Analysis Medium) "stalled@." ;
    stalled := true ;
    ignore (ProcLocker.try_lock (procname_of_pid ()) : bool)
  in
  let unmark () =
    if !stalled then (
      L.(debug Analysis Medium) "stalled@." ;
      stalled := false ;
      let pname = procname_of_pid () in
      if ProcLocker.is_locked ~proc_filename:(Procname.to_short_unique_name pname) then
        ProcLocker.unlock pname )
  in
  (mark, unmark)


(** Bypassed procedures which should not be unlocked at the end of the analysis. These are not
    necessarily component heads, so if we were to unlock them we could add a second entry point to a
    component, which we precisely want to avoid.*)
let bypassed = ref Procname.Set.empty

(** In case of deadlock (i.e. when all jobs are stalled), allow the process with lowest priority to
    bypass other processes' locks. *)
let can_bypass () =
  let priority = Priority.get () in
  let min_priority = Priority.minimum () in
  (* Declaring this as a function instead of an immediate value to delay evaluation and avoid
     potentially needless syscalls. *)
  let get_nb_stalled () =
    Sys.readdir procname_locks_path
    |> Array.filter ~f:(String.is_prefix ~prefix:stalled_prefix)
    |> Array.length
  in
  Int.(
    priority = min_priority && get_nb_stalled () = Config.jobs - ProcessPool.get_nb_idle_children () )


(** Procnames part of the component currently analyzed which have not yet been analyzed *)
let to_skip = ref Procname.Set.empty

let should_skip pname = Procname.Set.mem pname !to_skip

let mark_skipped pname = to_skip := Procname.Set.remove pname !to_skip

(** Heads of components currently being processed *)
let current_components = ref Procname.Set.empty

(** Mark all elements of the component as "to skip" and register the component *)
let take_component_ownership pname =
  L.(debug Analysis Medium) "taking ownership of %a@." Procname.pp pname ;
  let mark_owned pname = to_skip := Procname.Set.add pname !to_skip in
  let component_map = ComponentMap.data () in
  match ComponentMap.find_opt component_map pname with
  | None ->
      ()
  | Some component ->
      Procname.Set.iter mark_owned component ;
      current_components := Procname.Set.add pname !current_components ;
      (* Removing the current component from the map avoids needless iterations to mark it if it is
         encountered by the process again at some point. Since the component has already been
         analyzed, this will skip needless locking and unlocking of its procedures should they be
         met again. *)
      ComponentMap.remove component_map pname


let lock pname =
  if should_skip pname then (
    L.(debug Analysis Medium) "skipping %a@." Procname.pp pname ;
    mark_skipped pname )
  else (
    L.(debug Analysis Medium) "locking %a@." Procname.pp pname ;
    let count = ref 100 in
    try
      (* Repeatedly try to take the lock, regularly checking for possible bypass. *)
      while not (ProcLocker.try_lock pname) do
        (* Same as above. *)
        ComponentMap.remove (ComponentMap.data ()) pname ;
        ignore (Unix.nanosleep 0.01) ;
        (* We want to limit the number of filesystem checks for stalled jobs but not the number of
           checks for locks, hence the counter. *)
        if !count <= 0 then (
          mark_stalled () ;
          if can_bypass () then (
            L.(debug Analysis Medium) "bypassed %a@." Procname.pp pname ;
            raise Exit ) ;
          count := 100 )
        else decr count
      done ;
      unmark_stalled () ;
      Priority.push pname ;
      take_component_ownership pname
    with Exit ->
      unmark_stalled () ;
      bypassed := Procname.Set.add pname !bypassed )


let unlock pname =
  if Procname.Set.mem pname !bypassed then bypassed := Procname.Set.remove pname !bypassed
  else (
    L.(debug Analysis Medium) "unlocking %a@." Procname.pp pname ;
    ProcLocker.unlock pname ;
    Priority.pop pname ) ;
  if Procname.Set.mem pname !current_components then (
    L.(debug Analysis Medium) "finished component %a@." Procname.pp pname ;
    current_components := Procname.Set.remove pname !current_components )


let next_to_cleanup () =
  (*
   * If we finished processing all current components but some procedures are still marked as
   * "to_skip", we want to analyze them. This is to cope with code such as:
   *
   * if false; then
   *   some_function();
   * end if;
   *
   * `some_function` is statically called so it is present in the syntactic callgraph (and thus in
   * the component) but it is never reached dynamically and thus never analyzed.
   *)
  if Procname.Set.is_empty !current_components then
    Procname.Set.find_first_opt (fun _ -> true) !to_skip
  else None


(* Main scheduling *)

type target = TaskSchedulerTypes.target

type task_generator = (target, string) ProcessPool.TaskGenerator.t

let task_of_pname pname = TaskSchedulerTypes.Procname pname

(** Main scheduling function *)
let of_queue main_queue : task_generator =
  let remaining = ref (Queue.length main_queue) in
  let is_empty () = Int.equal !remaining 0 in
  let remaining_tasks () = !remaining in
  let current_head = ref None in
  let is_current_head task =
    match !current_head with None -> false | Some head -> TaskSchedulerTypes.equal head task
  in
  let finished ~result work =
    if is_current_head work then current_head := None ;
    match result with
    | None ->
        decr remaining
    | Some _ ->
        (* Tasks with dependencies are caught in {!lock} and should never be encountered here. *)
        L.die InternalError "Unexpected dependencies in ComponentScheduler"
  in
  let next () = Queue.dequeue main_queue in
  {remaining_tasks; is_empty; next; finished}


module SCC = Graph.Components.Make (struct
  type t = CallGraph.t

  module V = struct
    type t = CallGraph.Node.t

    let compare (l : t) (r : t) = Int.compare l.id r.id

    let hash (t : t) = Int.hash t.id

    let equal (l : t) (r : t) = Int.equal l.id r.id
  end

  let iter_vertex f = CallGraph.iter_vertex ~f

  let iter_succ f g src =
    CallGraph.iter_succ g src ~f:(fun dst ->
        let edge = CallGraph.Node.(src.pname, dst.pname) in
        (* Only process unmasked edges. *)
        if not (is_edge_masked edge) then f dst )
end)

let print_graph g name =
  let data =
    "digraph g {"
    :: List.fold ~init:[] g ~f:(fun acc (src, dst) ->
           let res =
             Format.sprintf "\t\"%s\" -> \"%s\";"
               (Procname.to_short_unique_name src)
               (Procname.to_short_unique_name dst)
           in
           res :: acc )
    @ ["}"]
  in
  Out_channel.write_lines name data


let simplify_large_components g scc =
  (* Get all vertices in graph [g] *)
  let vertices = ref [] in
  let () =
    CallGraph.iter_vertex g ~f:(fun node ->
        CallGraph.iter_succ g node ~f:(fun succ ->
            vertices := CallGraph.Node.(node.pname, succ.pname) :: !vertices ) )
  in
  (* List of edges in the large components before and after simplification of components. *)
  let components_before = ref [] in
  let components_after = ref [] in
  (* Number of large components and total number of edges they contain. *)
  let nb_large_components = ref 0 in
  let nb_large_comps_edges = ref 0 in
  (* Masked edges which should not be taken into account during analysis. *)
  let masked_edges = ref [] in
  let f component =
    if List.length component > large_component_size then (
      (* Initialize the map of out degrees. *)
      let out_degree =
        List.fold component ~init:Procname.Map.empty ~f:(fun acc pname ->
            Procname.Map.add pname (ref 0) acc )
      in
      (* Compute out degree of procedures within the component to other procedures within the
         component. *)
      List.iter !vertices ~f:(fun (src, dst) ->
          match Procname.Map.find_opt src out_degree with
          | Some d when Procname.Map.mem dst out_degree ->
              components_before := (src, dst) :: !components_before ;
              incr nb_large_comps_edges ;
              incr d
          | _ ->
              () ) ;
      (* Mask edges we want to simplify. *)
      List.iter !vertices ~f:(fun (src, dst) ->
          match (Procname.Map.find_opt src out_degree, Procname.Map.find_opt dst out_degree) with
          | Some outer, Some _ ->
              (* We use a simple heuristic: delete every edge going from one procedure within the
                 component to another procedure within the component when the source procedure
                 dispatches to 2 or less procedures within the component. This means that large
                 "switches" are unaffected, as well as edges which destination is in another
                 component. *)
              if !outer <= 2 then masked_edges := (src, dst) :: !masked_edges
              else components_after := (src, dst) :: !components_after
          | _ ->
              () ) )
  in
  List.iter scc ~f ;
  L.progress "Simplified %d out of %d edges of %d large components.@." (List.length !masked_edges)
    !nb_large_comps_edges !nb_large_components ;
  MaskedEdges.store (EdgeSet.of_list !masked_edges) ;
  (* Dump components before and after simplification in debug mode. *)
  if Config.debug_level_analysis > 0 then (
    print_graph !vertices @@ Config.results_dir ^/ "static_analysis_callgraph.dot" ;
    print_graph !components_before @@ Config.results_dir ^/ "raw_callgraph_components.dot" ;
    print_graph !components_after @@ Config.results_dir ^/ "simplified_callgraph_components.dot" )


let make sources =
  let syntactic_call_graph = SyntacticCallGraph.build_from_sources sources in
  (* [scc] is a function because we actually need to compute the components twice: first to detect
     and simplify large components, then to get a proper result taking simplified components into
     account. *)
  let scc () =
    SCC.scc_list syntactic_call_graph |> List.map ~f:(List.map ~f:(fun n -> n.CallGraph.Node.pname))
  in
  simplify_large_components syntactic_call_graph (scc ()) ;
  let component_map = ComponentMap.create 109 in
  let tails = ref [] in
  let priorities = ref PriorityMap.empty in
  let register_priority pname rank = priorities := PriorityMap.add pname rank !priorities in
  let f i = function
    | [] ->
        L.die InternalError "Component cannot be empty"
    | [pname] ->
        register_priority pname i ;
        pname
    | head :: tail ->
        register_priority head i ;
        tails := tail :: !tails ;
        let lock_exn pname =
          if not (ProcLocker.try_lock pname) then
            L.die InternalError "Locking twice %a@." Procname.pp pname
        in
        List.iter tail ~f:lock_exn ;
        ComponentMap.add component_map head (Procname.Set.of_list tail) ;
        head
  in
  let main_queue = scc () |> List.mapi ~f |> List.map ~f:task_of_pname |> Queue.of_list in
  ComponentMap.store component_map ;
  PriorityMap.store !priorities ;
  of_queue main_queue
