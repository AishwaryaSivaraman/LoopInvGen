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

let contains s1 s2 =
  let len1 = String.length s1
  and len2 = String.length s2 in
  if len1 < len2 then false else
    let rec aux i =
      if i < 0 then false else
        let sub = String.sub s1 i len2 in
        if (sub = s2) then true else aux (pred i)
    in
    aux (len1 - len2)

let print_results (result, post_condition, stats) =
  let open PIE in
  Stdio.(Out_channel.output_lines stdout [
    ("The postcondition is: " ^ (post_condition)) ;
    ("The precondition is: " ^ (cnf_opt_to_desc result)) ;
    ("  > Total time (ms): " ^ (Float.to_string stats.pi_time_ms)) ;
    ("  > Synth time (ms): [" ^ (Utils.List.to_string_map
                                    ~sep:"; " stats._Synthesizer
                                    ~f:(fun s -> Float.to_string (s.synth_time_ms)))
                              ^ "]") ;
    ""
  ])

let filterPostConditions (post_conditions: Synthesizer.result list)=
    List.filter ~f:(fun pc -> contains (pc.string) "res") post_conditions

let synthPostConditionExpressions ?(consts = []) ~(job : Job.te) ~(config : Synthesizer.Config.t)
                 ~(arg_types : Type.t list) stats
                 : Expr.synthesized Doubly_linked.t Array.t array =
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
      | Experimental (res, synth_stats) -> res, synth_stats
      | _ -> raise (Internal_Exn "Expecting a list of synthesized expressions")
  in stats._Synthesizer <- synth_stats :: stats._Synthesizer
     ; stats.te_time_ms <- stats.te_time_ms +. synth_stats.synth_time_ms
     ; result

let synthPreConditions ?(config = PIE.Config.default) ?(consts = []) (job : Job.te) (post_conditions ) =
  let pre_conditions = Array.fold ~init:[] (post_conditions)
                        ~f:(fun res cand_level -> Array.fold ~init:res (cand_level)
                                  ~f:(fun res cand_dlist -> (Doubly_linked.fold_right ~init:res
                                          ~f:(fun (candidate:Expr.synthesized) res ->
                                                begin
                                                    let pc_f = (Expr.to_function (candidate.expr))
                                                    in let job_unlab = (Job.create_unlabeled  ~f:job.f
                                                                        ~args:job.farg_f
                                                                        ~post:(fun inp res ->
                                                                                  match inp , res with
                                                                                  | _ , Error e -> false
                                                                                  | inp, Ok r -> let inputs = inp@(List.init 1 ~f:(fun i -> r))
                                                                                                    in match (pc_f inputs)
                                                                                                    (* in match (pc_f inp) *)
                                                                                                    with | Value.Bool y -> y | _ -> false )
                                                                        ~features:job.features 
                                                                          job.tests)
                                                    in let (result, stats) = PIE.learnPreCond ~config:config ~consts:consts job_unlab
                                                    in (print_results (result, (Expr.to_string (Array.of_list job.farg_names) candidate.expr), stats));
                                                    if (String.equal (cnf_opt_to_desc result) "false") then res
                                                    else res @ [(result, (Expr.to_string (Array.of_list job.farg_names) candidate.expr), stats)]
                                                end)
                                              cand_dlist)))
    in pre_conditions

(* let syntPreConditions ?(config = PIE.Config.default) ?(consts = []) (job : Job.te) 
                      (* (post_conditions: Synthesizer.result list) = *)
                      (post_conditions ) =
  let count = ref 0 in
  let pre_conditions =
      List.filter_map post_conditions
          ~f:(fun pc -> let pc_f = Expr.to_function pc.expr
                        in let job_unlab = (Job.create_unlabeled  ~f:job.f
                                                                  ~args:job.farg_f
                                                                  ~post:(fun inp res ->
                                                                            match inp , res with
                                                                            | _ , Error e -> false
                                                                            | inp, Ok r -> let inputs = inp@(List.init 1 ~f:(fun i -> r))
                                                                                              in match (pc_f inputs)
                                                                                              (* in match (pc_f inp) *)
                                                                                              with | Value.Bool y -> y | _ -> false )
                                                                  ~features:job.features 
                                                                    job.tests)
                        in let (result, stats) = PIE.learnPreCond ~config:config ~consts:consts job_unlab
                        in
                        (* Stdio.print_endline ("  \n Postcondition is: " ^ (pc.string) ^
                                   " Precondition is: " ^ ((cnf_opt_to_desc result))); *)
                          (* Stdio.print_endline ("\n count is "^ (Int.to_string !count) ^ "/" ^ (Int.to_string (List.length post_conditions)));
                          count := !count + 1; *)
                        Log.debug (lazy ("  \n Postcondition is: " ^ (pc.string) ^
                                   " Precondition is: " ^ ((cnf_opt_to_desc result))));
                        if (String.equal (cnf_opt_to_desc result) "false") then None
                        else Some (result, pc.string, stats)
                ) in pre_conditions *)

let learnLemma ?(config = Config.default) ?(consts = []) (job : Job.te) =
  let start_time = Time.now () in
  let te_stats = {_PIE = [] ; _Synthesizer = []; te_time_ms = 0.0 }
  in let post_conditions = synthPostConditionExpressions ~consts:consts ~job:job ~config:{config._Synthesizer with cost_limit = config.max_expression_size} ~arg_types:job.farg_types te_stats
     in let pre_conditions = synthPreConditions ~config:{config._PIE with _Synthesizer = {config._Synthesizer with prune_obs_equivalen_expr = true}} ~consts:consts job ( post_conditions)
     in te_stats.te_time_ms <- te_stats.te_time_ms
                                 +. Time.(Span.(to_ms (diff (now ()) start_time)))
              ; (pre_conditions, te_stats)