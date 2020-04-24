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

let te_append_job =
  let open Value in
  let open Type in
  Job.create_te
    ~f:(fun [@warning "-8"] [ List (INT, l1) ; List (INT, l2) ]
        -> List (INT, (l1 @ l2)))
    ~args:([ ("l1", Type.(LIST INT)) ; ("l2", Type.(LIST INT)); ("res", Type.(LIST INT)) ])
    ~args_pie: ([ ("l1", Type.(LIST INT)) ; ("l2", Type.(LIST INT)); ])
    ~features:[]
    (List.map2_exn ~f:(fun l1 l2 -> [l1;l2])
            Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 100
                 (TestGen.for_type (Type.LIST Type.INT))))
            Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 100
                 (TestGen.for_type (Type.LIST Type.INT)))))

let with_synth_TE_append () =
  Stdio.print_endline "TE for { res = l1@l2 } with feature learning:" ;
  let (pre_conditions, stats) =
          TE.learnLemma
          ~config:{TE.Config.default
                             with max_expression_size = 8
                                ; _Synthesizer = {Synthesizer.Config.default
                                                      with logic = Logic.of_string "ALL" ; cost_limit = 10}}
           te_append_job
  in Stdio.print_endline ("TE Complete")


let te_cons_job =
  let open Value in
  let open Type in
  Job.create_te
    ~f:(fun [@warning "-8"] [ x ; List (INT, l) ]
        -> List (INT, (x::l)))
    ~args:([ ("x", Type.INT) ; ("l", Type.(LIST INT)); ("res", Type.(LIST INT)) ])
    ~args_pie: ([ ("x", Type.INT) ; ("l", Type.(LIST INT)); ])
    ~features:[]
    (List.map2_exn ~f:(fun l1 l2 -> [l1;l2]) 
            Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type Type.INT)))
            Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type (Type.LIST Type.INT)))))

let with_synth_TE_cons () =
  Stdio.print_endline "TE for { res = cons x l } with feature learning:" ;
  let (pre_conditions, stats) =
            TE.learnLemma
            ~config:{TE.Config.default
                               with max_expression_size = 8
                                  ; _Synthesizer = {Synthesizer.Config.default
                                                      with logic = Logic.of_string "ALL"; cost_limit = 8}}
            te_cons_job
  in Stdio.print_endline ("TE Complete")


let te_skip_job =
  let open Value in
  let open Type in
  let x = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type Type.INT)))
    in let a = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type Type.INT)))
    in let l = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type (Type.LIST Type.INT))))
    in let l' = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type (Type.LIST Type.INT))))
    in let l'' = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type (Type.LIST Type.INT))))
    in let tests = (List.mapi ~f:(fun i xs -> match List.nth x i with
                                             | None -> raise (Failure "error")
                                             | Some e -> match (List.nth a i) with
                                                         | None -> raise (Failure "error")
                                                         | Some e' -> match (List.nth l' i) with
                                                         | None -> raise (Failure "error")
                                                         | Some ys -> match (List.nth l'' i) with
                                                         | None -> raise (Failure "error")
                                                         | Some zs -> [ e; e'; ys ;xs; zs]) l)
  in
  Job.create_te
    ~f:(fun _ -> Value.Bool true)
    ~args:([ ("x", Type.INT) ; ("a", Type.INT); ("l1", Type.(LIST INT)); ("l2", Type.(LIST INT)); ("l3", Type.(LIST INT));])
    ~args_pie: ([ ("x", Type.INT) ; ("a", Type.INT); ("l1", Type.(LIST INT)); ("l2", Type.(LIST INT)); ("l3", Type.(LIST INT));])
    ~features:[]
     (tests)

let with_synth_TE_skip () =
  Stdio.print_endline "TE for { skip; } with feature learning:" ;
  let (pre_conditions, stats) =
            TE.learnLemma
            ~config:{TE.Config.default
                               with max_expression_size = 2
                                  ; _Synthesizer = {Synthesizer.Config.default
                                                      with logic = Logic.of_string "ALL"; cost_limit = 20}
                    }
            te_skip_job
  in Stdio.print_endline ("TE Complete")

let te_composition_job =
  let open Value in
  let open Type in
  let x = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type Type.INT)))
    in let l1 = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type (Type.LIST Type.INT))))
    in let l2 = Quickcheck.(random_value ~seed:`Nondeterministic
              (Generator.list_with_length 1000
                 (TestGen.for_type (Type.LIST Type.INT))))
    in let tests = (List.mapi ~f:(fun i l -> match List.nth x i with
                                             | None -> raise (Failure "error")
                                             | Some e -> match (List.nth l1 i) with
                                                         | None -> raise (Failure "error")
                                                         | Some l' -> [ e; l'; l]) l2)
  in
  Job.create_te
    ~f:(fun [@warning "-8"] [ x ; List (INT, l1);List (INT, l2) ]-> List (INT, l1 @ x::l2))
    ~args:([ ("x", Type.INT) ; ("l1", Type.(LIST INT)); ("l2", Type.(LIST INT)); ("res", Type.(LIST INT)); ])
    ~args_pie: ([ ("x", Type.INT) ; ("l1", Type.(LIST INT)); ("l2", Type.(LIST INT)); ])
    ~features:[]
     (tests)

let with_synth_TE_composition () =
  Stdio.print_endline "TE for { res = x :: (l1 @ l2); } with feature learning:" ;
  let (pre_conditions, stats) =
            TE.learnLemma
            ~config:{TE.Config.default
                               with max_expression_size = 8
                                  ; _Synthesizer = {Synthesizer.Config.default
                                                      with logic = Logic.of_string "ALL"; cost_limit = 8}
                    }
            te_composition_job
  in Stdio.print_endline ("TE Complete")

let () =
        Log.enable ~msg:"APP" (Some "te_log") ;
        with_synth_TE_skip ();