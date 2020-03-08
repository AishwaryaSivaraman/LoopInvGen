open Core_kernel

open Exceptions
open Utils
open PIE


module Config = struct
  type t = {
    _Synthesizer : Synthesizer.Config.t ;
    _PIE : PIE.Config.t;
    max_expression_size: int;
  }

  let default : t = {
    _Synthesizer = Synthesizer.Config.default ;
    _PIE = PIE.Config.default;
    max_expression_size = 5 ;
  }
end

type stats = {
  mutable te_time_ms : float ;
  mutable _PIE : PIE.stats list ;
  mutable _Synthesizer : Synthesizer.stats list;
} [@@deriving sexp]

let synthPostConditionExpressions ?(consts = []) ~(job : Job.te) ~(config : Synthesizer.Config.t)
                 ~(arg_types : Type.t list) stats
                 : Synthesizer.result list =
  let open Synthesizer in
  let open Quickcheck in
  let result, synth_stats =
    match solve ~config:{config with goal_directed = false
                                                         ;prune_obs_equivalen_expr = false}
                {
                  constants = consts ;
                  arg_names = job.farg_names ;
                  inputs = List.map job.farg_types
                                    ~f:(fun t -> Array.init 2 ~f:(fun i -> random_value (TestGen.for_type t)));
                  outputs = Array.init 2 ~f:(fun i -> random_value (TestGen.for_type Type.BOOL))
                } 
    with
      | All (res, synth_stats) -> res, synth_stats
      | _ -> raise (Internal_Exn "Expecting a list of synthesized expressions")
  in stats._Synthesizer <- synth_stats :: stats._Synthesizer
     ; stats.te_time_ms <- stats.te_time_ms +. synth_stats.synth_time_ms
     ; result

let syntPreConditions ?(config = PIE.Config.default) ?(consts = []) (job : Job.te) (post_conditions: Synthesizer.result list) =
  let pre_conditions = 
      List.map post_conditions
          ~f:(fun pc -> let pc_f = Expr.to_function pc.expr
                        in let job_unlab = (Job.create_unlabeled  ~f:job.f
                                                                  ~args:job.farg_f
                                                                  ~post:(fun inp res ->
                                                                            match inp , res with
                                                                            | _ , Error e -> false
                                                                            | inp, Ok r -> let inputs = inp@(List.init 1 ~f:(fun i -> r))
                                                                                              in match (pc_f inputs)
                                                                                              with | Value.Bool y -> y | _ -> false )
                                                                  ~features:job.features 
                                                                    job.tests)
                        in let (result, stats) = PIE.learnPreCond ~config:config ~consts:consts job_unlab in (result, pc.string, stats)
                ) in pre_conditions

let learnLemma ?(config = Config.default) ?(consts = []) (job : Job.te) =
  let start_time = Time.now () in
  let te_stats = {_PIE = [] ; _Synthesizer = []; te_time_ms = 0.0 }
  in let post_conditions = synthPostConditionExpressions ~consts:consts ~job:job ~config:{config._Synthesizer with cost_limit = config.max_expression_size} ~arg_types:job.farg_types te_stats
     in let pre_conditions = syntPreConditions ~config:config._PIE ~consts:consts job post_conditions
     in te_stats.te_time_ms <- te_stats.te_time_ms
                                 +. Time.(Span.(to_ms (diff (now ()) start_time)))
              ; (pre_conditions, te_stats)