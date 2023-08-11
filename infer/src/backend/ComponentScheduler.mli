(*
 * Copyright (c) 2017-present, AdaCore.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

(*
 * This scheduler's goal is to be deterministic through the scheduling of strongly connected
 * components of the syntactic callgraph instead of lone procedures. This removes the biggest source
 * of non-determinism in analyses, which is parallel processing of nodes in a cycle -- which may
 * have different results depending on which node of the cycle is processed first.
 *)

type target = TaskSchedulerTypes.target

type task_generator = (target, string) ProcessPool.TaskGenerator.t

val is_edge_masked : Procname.t * Procname.t -> bool

val lock : Procname.t -> unit

val unlock : Procname.t -> unit

val next_to_cleanup : unit -> Procname.t option

val make : SourceFile.t list -> task_generator
