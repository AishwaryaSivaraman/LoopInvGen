open Core_kernel

open LoopInvGen

let print_PI_results (result, post_condition, stats) =
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

(* a job for inferring a precondition to ensure that the absolute value
   function has a result equal to its argument *)
let abs_job = Job.create_unlabeled
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ ("x", Type.INT) ])
  ~post:(fun inp res ->
          match [@warning "-8"] inp , res with
          | [ Value.Int x ], Ok (Value.Int y) -> x = y)
  (* We start with no initial features *)
  ~features:[]
  (* We have a random generator for Type.INT.
   * We generate 64 random Value.Int elements
   * and then wrap them in singleton lists (single arguments to abs). *)
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

let with_synth_PI () =
  Stdio.print_endline "PI for { x = abs(x) } with feature learning:" ;
  let (result, stats) = PIE.learnPreCond abs_job
  in print_PI_results (result, "x=y", stats)

let te_abs_job = Job.create_te
  ~f:(fun [@warning "-8"] [ Value.Int x ] -> Value.Int (if x > 0 then x else -x))
  ~args:([ ("x", Type.INT); ("res", Type.INT) ])
  ~args_pie: ([ ("x", Type.INT) ])
  ~features:[]
  (List.map ~f:(fun i -> [ i ])
            Quickcheck.(random_value
              (Generator.list_with_length 64
                 (TestGen.for_type Type.INT))))

let with_synth_TE () =
  Stdio.print_endline "TE for { x = abs(x) } with feature learning:" ;
  let (pre_conditions, stats) = TE.learnLemma ~config:{TE.Config.default with max_expression_size = 4} te_abs_job
  in List.iter ~f:(fun pc -> print_PI_results pc) pre_conditions

(* a job for inferring a precondition to check when the result of appending
   two (integer) lists is an empty list *)
let append_job =
  let open Value in
  let open Type in
  Job.create_unlabeled
    ~f:(fun [@warning "-8"] [ List (INT, x) ; List (INT, y) ]
        -> List (INT, (x @ y)))
    ~args:([ ("x", Type.(LIST INT)) ; ("y", Type.(LIST INT)) ])
    ~post:(fun inp res ->
            match [@warning "-8"] inp , res with
            | [ List _ ; List _ ] , Ok (List (INT, res)) -> List.is_empty res)
    (* We start with these two features and disable feature synthesis *)
    ~features:[
      ((fun [@warning "-8"] [ List (INT, list1) ; _ ] -> List.is_empty list1),
       "(= x [])") ;
      ((fun [@warning "-8"] [ _ ; List (INT, list2) ] -> List.is_empty list2),
       "(= y [])") ;
    ]
    (* Generators for Type.LIST are not yet implemented. *)
    (List.map [ ([], [])
              ; ([Int 1 ; Int 2], [Int 3])
              ; ([Int 4], [])
              ; ([], [Int 5]) ]
              ~f:(fun (l1,l2) -> [ List (INT, l1) ; List (INT, l2) ]))

let no_synth_PI () =
  Stdio.print_endline "PI for { append(l1,l2) = [] } without feature learning:" ;
  let (result, stats) = PIE.learnPreCond append_job
                     ~config:{ PIE.Config.default with disable_synth = true }
  in print_PI_results (result, "res = []", stats)


let () = with_synth_TE ()