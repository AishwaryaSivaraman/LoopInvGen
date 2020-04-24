open Base

open LoopInvGen

let zip_eval = (List.find_exn ListComponents.all
                                ~f:(fun comp -> String.equal comp.name "zip")).evaluate

let zip () =
  let list1 = Value.List (Type.INT, [Value.Int 3;Value.Int 10]) in
  let list2 = Value.List (Type.INT, [Value.Int 4;]) in
  let select_ret = zip_eval [list1; list2] in 
  Stdio.print_endline ("\n" ^ (Value.to_string select_ret));
  let res = Value.equal select_ret (Value.List (Type.INT, [Value.Tuple (3, 4)]))
   in Alcotest.(check bool) "identical" true res

let all = [
  "zip",                   `Quick, zip ;
]