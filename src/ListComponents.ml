open Base

open Expr

let all_qf = [
  {
    name = "equal";
    codomain = Type.BOOL;
    domain = Type.[LIST (TVAR "T1"); LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l1); List (_,l2)]
                          -> if Int.equal (List.length l1) (List.length l2)
                                then Value.Bool (List.fold_left ~init:true ~f:(fun accum i -> accum && i) (List.map2_exn ~f:(fun i j -> Value.equal i j) l1 l2))
                                else Value.Bool false);
    to_string = (fun [@warning "-8"] [a; b] -> "(equal " ^ a ^ " " ^ b ^")");
    global_constraints = (fun _ -> [])
  } ;
  
  {
    name = "append";
    codomain = Type.(LIST (TVAR "T1"));
    domain = Type.[LIST (TVAR "T1"); LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (t,l1); List (_,l2)]
                          -> Value.List (t, l1@l2));
    to_string = (fun [@warning "-8"] [a; b] -> "(" ^ a ^ " @ " ^ b ^")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "zip";
    codomain = Type.(LIST (TVAR "T1"));
    domain = Type.[LIST (TVAR "T1"); LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (t,l1); List (_,l2)]
                          ->(let l = (List.mapi ~f:(fun i x ->
                                                              (match (List.nth l1 i), (List.nth l2 i) with
                                                                | Some (Value.Int e1), Some (Value.Int e2) -> (Value.Tuple (e1, e2))
                                                                | _ , _ -> raise (Failure "error")
                                                              )) l2) 
                                                              in Value.List (t, l)));
    to_string = (fun [@warning "-8"] [a; b] -> "(zip " ^ a ^ " " ^ b ^")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "empty";
    codomain = Type.BOOL;
    domain = Type.[LIST (TVAR "_")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)] -> if Int.equal (List.length l) 0 then Value.Bool true else Value.Bool false);
    to_string = (fun [@warning "-8"] [a] -> "([] = " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
   {
    name = "length";
    codomain = Type.INT;
    domain = Type.[LIST (TVAR "_")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)] -> Int (List.length l));
    to_string = (fun [@warning "-8"] [a] -> "(len " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "hd";
    codomain = Type.TVAR "T1";
    domain = Type.[LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)] -> List.hd_exn l);
    to_string = (fun [@warning "-8"] [a] -> "(hd " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "tl";
    codomain = Type.(LIST (TVAR "T1"));
    domain = Type.[LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (t,l)] -> List (t, (List.tl_exn l)));
    to_string = (fun [@warning "-8"] [a] -> "(tl " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  };
  {
    name = "cons";
    codomain = Type.(LIST (TVAR "T1"));
    domain = Type.[(TVAR "T1"); LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [a; List (t,l)] -> List (t, (List.cons a l)));
    to_string = (fun [@warning "-8"] [a; l] -> "(cons " ^ a ^ " " ^ l ^")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "In";
    codomain = Type.BOOL;
    domain = Type.[(TVAR "T1"); LIST (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [a; List (t,l)] -> (Value.Bool (List.fold_left ~f:(fun b x -> b || x = a) ~init:false l)));
    to_string = (fun [@warning "-8"] [a; l] -> "(In " ^ a ^ " " ^ l ^")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "nth";
    codomain = Type.TVAR "T1";
    domain = Type.[LIST (TVAR "T1"); INT; (TVAR "T1")];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l); Int n; default] -> match (List.nth l n) with
                                                                 | Some v -> v
                                                                 | _ -> default);
    to_string = (fun [@warning "-8"] [a; n; d] -> "(nth " ^ a ^ " " ^ n ^ " " ^ d ^")");
    global_constraints = (fun _ -> [])
  } ;
]

let all = all_qf @ [
  {
    name = "all";
    codomain = Type.BOOL;
    domain = Type.[LIST BOOL];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)]
                      -> Bool (List.for_all l ~f:(fun [@warning "-8"] (Bool b) -> b)));
    to_string = (fun [@warning "-8"] [a] -> "(all " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  } ;
  {
    name = "any";
    codomain = Type.BOOL;
    domain = Type.[LIST BOOL];
    is_argument_valid = (function _ -> true);
    evaluate = Value.(fun [@warning "-8"] [List (_,l)]
                      -> Bool (List.exists l ~f:(fun [@warning "-8"] (Bool b) -> b)));
    to_string = (fun [@warning "-8"] [a] -> "(any " ^ a ^ ")");
    global_constraints = (fun _ -> [])
  }
]

let map_transform_unary (component : component) : component =
  match component.domain with
  | [dom] -> let name = "map-" ^ component.name
              in { name;
                   codomain = Type.LIST component.codomain;
                   domain = Type.[LIST dom];
                   is_argument_valid = (function _ -> true);
                   evaluate = Value.(fun [@warning "-8"] [ List (_,l) ]
                                     -> List ((Type.LIST component.codomain),
                                              (List.map l ~f:(fun e -> component.evaluate [e]))));
                   to_string = (fun [@warning "-8"] [a] -> "(" ^ name ^ " " ^ a ^ ")" );
                   global_constraints = (fun _ -> [])
                  }
  | l -> raise (Exceptions.Transformation_Exn (
                  "Cannot transform a " ^ (Int.to_string (List.length l)) ^ "-ary component " ^ component.name))

let all_transformed_int_unary =
  all @ (List.filter_map (BooleanComponents.all @ IntegerComponents.polynomials)
                         ~f:(fun c -> try Some (map_transform_unary c)
                                      with _ -> None))

(* FIXME: We create two map versions of each binary component:
          One that fixes the first argument and another that fixes the second.
          However, these would be equivalent for commutative components;
          so may be keep a `commutative` attribute for each component,
          or, implement a better, more general strategy for component transformation. *)

let map_transform_binary (component : component) : component list =
  match component.domain with
  | [d1 ; d2]
    -> let nameL = "map-fixL-" ^ component.name in
       let nameR = "map-fixR-" ^ component.name
        in [{
              name = nameR;
              codomain = Type.LIST component.codomain;
              domain = Type.[LIST d1 ; d2];
              is_argument_valid = (function _ -> true);
              evaluate = Value.(fun [@warning "-8"] [List (_, x) ; y]
                                -> List (component.codomain, (List.map x ~f:(fun e -> component.evaluate [e ; y]))));
              to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ nameR ^ " " ^ a ^ " " ^ b ^ ")");
              global_constraints = component.global_constraints
            } ;
            {
              name = nameL;
              codomain = Type.LIST component.codomain;
              domain = Type.[d1 ; LIST d2];
              is_argument_valid = (function _ -> true);
              evaluate = Value.(fun [@warning "-8"] [x ; List (_, y)]
                                -> List (component.codomain, (List.map y ~f:(fun e -> component.evaluate [x ; e]))));
              to_string = (fun [@warning "-8"] [a ; b] -> "(" ^ nameL ^ " " ^ a ^ " " ^ b ^ ")");
              global_constraints = component.global_constraints
            }]
  | l -> raise (Exceptions.Transformation_Exn (
                  "Cannot transform a " ^ (Int.to_string (List.length l)) ^
                  "-ary component " ^ component.name))

let all_transformed_int_binary =
  all_transformed_int_unary @
  List.(concat (filter_map (BooleanComponents.all @ IntegerComponents.polynomials)
                           ~f:(fun c -> try Some (map_transform_binary c)
                                        with _ -> None)))

let levels = [| all_qf ; all ; all_transformed_int_unary ; all_transformed_int_binary |]