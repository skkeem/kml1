(*
 * SNU 4541.664A Program Analysis 2017 Spring
 * K- Interpreter Solution
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)


(*
 * K- Interpreter
 *)

module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
      | NUM of int
      | VAR of id
      | ADD of exp * exp
	  | MINUS of exp
	  | TRUE
	  | FALSE
	  | NOT of exp
	  | ANDALSO of exp * exp
	  | ORELSE of exp * exp
	  | LESS of exp * exp
  
  type cmd =
      | SKIP
      | SEQ of cmd * cmd        (* sequence *)
      | IF of exp * cmd * cmd   (* if-then-else *)
	  | WHILE of exp * cmd      (* while *)
      | ASSIGN of id * exp      (* assgin to variable *)

  type program = cmd
  type memory
  type value

  val botMemory : memory
  val eval : memory * exp -> value  (* exp eval *)
  val assume : memory * exp -> memory (* memory filtering *)
  val assumeNot : memory * exp -> memory (* memory filtering *)
  val analyzer : memory * program -> memory
  val used_varlist : program -> id list
  val pp_memory : memory -> id list -> unit
end

module K : KMINUS =
struct
  exception Error of string
  type id = string
  type exp =
      | NUM of int
      | VAR of id
      | ADD of exp * exp
	  | MINUS of exp
	  | TRUE
	  | FALSE
	  | NOT of exp
	  | ANDALSO of exp * exp
	  | ORELSE of exp * exp
	  | LESS of exp * exp
  
  type cmd =
      | SKIP
      | SEQ of cmd * cmd        (* sequence *)
      | IF of exp * cmd * cmd   (* if-then-else *)
	  | WHILE of exp * cmd      (* while *)
      | ASSIGN of id * exp      (* assgin to variable *)

  type program = cmd
  
  (* abstract domain type : "do not" change here *)
  type bound = MIN | Z of int | MAX
  type itv = ITV of bound * bound | BOT_ITV
  type bool_hat = TOP_BOOL | T | F | BOT_BOOL
 
  (* abstract memory, value type : "do not" change here *)
  type value = itv * bool_hat
  type memory = id -> value
 
  (* bottom values *)
  let botValue = (BOT_ITV, BOT_BOOL)
  let botMemory = fun x -> botValue

  (* top values *)
  let topValue = (ITV (MIN, MAX), TOP_BOOL)
  let topMemory = fun x -> topValue
  
  (* memory operation *)
  let store mem id v = fun x -> if (x = id) then v else mem(x)
  
  let rec compare_mem m1 m2 varlist =
    match varlist with
	| [] -> true
	| hd::tl -> (m1(hd) = m2(hd)) && (compare_mem m1 m2 tl)
 
  let smaller_itv itv1 itv2 = 
    match (itv1, itv2) with
    | (BOT_ITV, _) -> true
    | (_, ITV (MIN, MAX)) -> true
    | (ITV (Z p1, Z q1), ITV (Z p2, Z q2)) -> (p2 <= p1) && (q1 <= q2)
    | (ITV (MIN, Z q1), ITV (MIN, Z q2)) -> (q1 <= q2)
    | (ITV (Z p1, MAX), ITV (Z p2, MAX)) -> (p1 <= p2)
    | _ -> false

  let smaller_bool b1 b2 = 
    match (b1, b2) with
    | (BOT_BOOL, _) -> true
    | (_, TOP_BOOL) -> true
    | (b1, b2) -> (b1 = b2)
    | _ -> false

  let smaller_val v1 v2 = 
    match (v1, v2) with
    | ((i1, b1), (i2, b2)) -> (smaller_itv i1 i2) && (smaller_bool b1 b2)

  let rec smaller_mem m1 m2 varlist =
    match varlist with
	| [] -> true
	| hd::tl -> (smaller_val (m1(hd)) (m2(hd))) && (smaller_mem m1 m2 tl)
    
  (* memory pretty print : "do not" change here *)
  let pp_bound : bound -> unit = fun bnd ->
    match bnd with
	| MIN -> print_string("MIN")
	| Z i -> print_int(i)
	| MAX -> print_string("MAX")

  let pp_itv : itv -> unit = fun itv ->
    match itv with
	| BOT_ITV -> print_string("bottom")
	| ITV (bnd1, bnd2) -> 
	  let _ = print_string("[") in
	  let _ = pp_bound(bnd1) in
	  let _ = print_string(", ") in
	  let _ = pp_bound(bnd2) in
	  print_string("]")
	  
  let pp_bool : bool_hat -> unit = fun b ->
    match b with
	| BOT_BOOL -> print_string("bottom") 
	| T -> print_string("T")
	| F -> print_string("F")
	| TOP_BOOL -> print_string("T, F")

  let rec pp_memory : memory -> id list -> unit = fun mem -> (fun varlist ->
    match varlist with
	| [] -> ()
	| hd::tl ->
	  let (itv, b) = mem(hd) in
	  let _ = print_string(hd ^ " -> interval : ") in
	  let _ = pp_itv(itv) in
	  let _ = print_string(" bool : ") in
	  let _ = pp_bool(b) in
	  let _ = print_newline() in
	  pp_memory mem tl
	  )
	 
  (* var list gathering : "do not" change here *)
  let rec list_trim l =
    match l with
	| [] -> []
	| hd::tl -> if (List.mem hd tl) then list_trim tl else hd::(list_trim tl)

  let rec used_vars_exp exp =
      (match exp with
      | NUM i -> []
      | VAR id -> id::[]
      | ADD (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  | MINUS e -> used_vars_exp e
	  | TRUE -> []
	  | FALSE -> []
	  | NOT e -> used_vars_exp e
	  | ANDALSO (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  | ORELSE (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  | LESS (e1, e2) -> (used_vars_exp e1) @ (used_vars_exp e2)
	  )
  
  let rec used_vars cmd =
	match cmd with
	| SKIP -> []
	| SEQ (cmd1, cmd2) -> (used_vars cmd1) @ (used_vars cmd2)
	| IF (e, cmd1, cmd2) -> (used_vars_exp e) @ (used_vars cmd1) @ (used_vars cmd2)
	| WHILE (e, cmd) -> (used_vars_exp e) @ (used_vars cmd)
	| ASSIGN (id, e) -> id::(used_vars_exp e)

  let used_varlist cmd = list_trim (used_vars cmd)
 
  (* join operaters : you may need these operaters *)
  let join_interval (itv1, itv2) =
      match (itv1, itv2) with
      | (BOT_ITV, i) -> i
      | (i, BOT_ITV) -> i
      | (ITV (Z p1, Z q1), ITV (Z p2, Z q2)) -> (ITV (Z (min p1 p2), Z (max q1 q2)))
      | (ITV (MIN, Z q1), ITV (_, Z q2)) -> (ITV (MIN, Z (max q1 q2)))
      | (ITV (_, Z q1), ITV (MIN, Z q2)) -> (ITV (MIN, Z (max q1 q2)))
      | (ITV (Z p1, MAX), ITV (Z p2, _)) -> (ITV (Z (min p1 p2), MAX))
      | (ITV (Z p1, _), ITV (Z p2, MAX)) -> (ITV (Z (min p1 p2), MAX))
      | _ -> (ITV (MIN, MAX))
  let join_bool (bool1, bool2) =
      match (bool1, bool2) with
      | (BOT_BOOL, b) -> b
      | (b, BOT_BOOL) -> b
      | _ -> TOP_BOOL
  let join_value (val1, val2) =
      match (val1, val2) with
      | ((i1, b1), (i2, b2)) -> (join_interval (i1, i2), join_bool (b1, b2))
  let rec join_memory (mem1, mem2) varlist =
    match varlist with
	| [] -> botMemory
	| hd::tl -> store (join_memory (mem1, mem2) tl) hd (join_value ((mem1 hd), (mem2 hd)))
  
  (* widening operaters : you may need these operaters *)
  let widenItv i1 i2=
      match (i1, i2) with
      | (BOT_ITV, i) -> i
      | (i, BOT_ITV) -> i
      | (ITV (Z p1, Z q1), ITV (Z p2, Z q2)) -> if p1 <= p2 then (if q1 < q2 then ITV (Z p1, MAX) else ITV (Z p1, Z q1)) else (if q1 < q2 then ITV (MIN, MAX) else ITV (MIN, Z q1))
      | (ITV (Z p1, _), ITV (Z p2, MAX)) -> if p1 <= p2 then ITV (Z p1, MAX) else ITV (MIN, MAX)
      | (ITV (_, Z q1), ITV (MIN, Z q2)) -> if q1 < q2 then ITV (MIN, MAX) else ITV (MIN, Z q1)
      | _ -> ITV (MIN, MAX)

  let widenVal v1 v2 =
      match (v1, v2) with
      | ((i1, b1), (i2, b2)) -> ((widenItv i1 i2), (join_bool (b1, b2)))

  let rec widenOp x y varlist =
      match varlist with
      | [] -> botMemory
      | hd::tl -> store (widenOp x y tl) hd (widenVal (x hd) (y hd))

  let widen ftn varlist =
      let x = ref botMemory in
      while not (smaller_mem (ftn !x) !x varlist) do
          x := widenOp !x (ftn !x) varlist
      done;
      !x

  (* narrowing operaters : you may need these operaters *)
  let narrowItv i1 i2=
      match (i1, i2) with
      | (BOT_ITV, i) -> BOT_ITV
      | (i, BOT_ITV) -> BOT_ITV
      | (ITV (MIN, Z q1), ITV (Z p2, _)) -> ITV (Z p2, Z q1)
      | (ITV (Z p1, MAX), ITV (_, Z q2)) -> ITV (Z p1, Z q2)
      | (ITV (MIN, MAX), _) -> i2
      | _ -> i1

  let narrowVal v1 v2 =
      match (v1, v2) with
      | ((i1, b1), (i2, b2)) -> ((narrowItv i1 i2), b2)

  let rec narrowOp x y varlist =
      match varlist with
      | [] -> botMemory
      | hd::tl -> store (narrowOp x y tl) hd (narrowVal (x hd) (y hd))

  let narrow m ftn varlist =
      let x = ref m in
      let y = ref (narrowOp !x (ftn !x) varlist) in
      while not (smaller_mem !x !y varlist) do
          x := !y;
          y := narrowOp !x (ftn !x) varlist
      done;
      !x
 
  (* exp evaluation : TODO you have to implement this *)
  let rec eval : (memory * exp) -> value  = fun (mem, e) ->
    match e with
	| NUM n -> (ITV (Z n, Z n), BOT_BOOL)
    | TRUE -> (BOT_ITV, T)
    | FALSE -> (BOT_ITV, F)
	| VAR x -> mem(x)
	| ADD (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                       | ((BOT_ITV, _), (_, _)) -> botValue
                       | ((_, _), (BOT_ITV, _)) -> botValue
                       | ((ITV (Z p1, Z q1), _), (ITV (Z p2, Z q2), _)) -> (ITV (Z (p1+p2), Z (q1+q2)), BOT_BOOL)
                       | ((ITV (Z p1, MAX), _), (ITV (Z p2, _), _)) -> (ITV (Z (p1+p2), MAX), BOT_BOOL)
                       | ((ITV (Z p1, _), _), (ITV (Z p2, MAX), _)) -> (ITV (Z (p1+p2), MAX), BOT_BOOL)
                       | _ -> topValue)
    | MINUS e -> (match (eval (mem, e)) with
                  | (BOT_ITV, _) -> botValue
                  | (ITV (Z p, Z q), _) -> (ITV (Z (-q), Z (-p)), BOT_BOOL)
                  | (ITV (MIN, Z q), _) -> (ITV (Z (-q), MAX), BOT_BOOL)
                  | (ITV (Z p, MAX), _) -> (ITV (MIN, Z (-p)), BOT_BOOL)
                  | (ITV (MIN, MAX), _) -> (ITV (MIN, MAX), BOT_BOOL)
                  | _ -> topValue)
    | ANDALSO (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                           | ((_, BOT_BOOL), (_, _)) -> botValue
                           | ((_, _), (_, BOT_BOOL)) -> botValue
                           | ((_, F), (_, _)) -> (BOT_ITV, F)
                           | ((_, _), (_, F)) -> (BOT_ITV, F)
                           | ((_, T), (_, T)) -> (BOT_ITV, T)
                           | ((_, TOP_BOOL), (_, _)) -> (BOT_ITV, TOP_BOOL)
                           | ((_, _), (_, TOP_BOOL)) -> (BOT_ITV, TOP_BOOL)
                           | _ -> topValue)
    | ORELSE (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                          | ((_, BOT_BOOL), (_, _)) -> botValue
                          | ((_, _), (_, BOT_BOOL)) -> botValue
                          | ((_, T), (_, _)) -> (BOT_ITV, T)
                          | ((_, _), (_, T)) -> (BOT_ITV, T)
                          | ((_, F), (_, F)) -> (BOT_ITV, F)
                          | ((_, TOP_BOOL), (_, _)) -> (BOT_ITV, TOP_BOOL)
                          | ((_, _), (_, TOP_BOOL)) -> (BOT_ITV, TOP_BOOL)
                          | _ -> topValue)
    | NOT e -> (match (eval (mem, e)) with
                | (_, BOT_BOOL) -> botValue
                | (_, T) -> (BOT_ITV, F)
                | (_, F) -> (BOT_ITV, T)
                | (_, TOP_BOOL) -> (BOT_ITV, TOP_BOOL)
                | _ -> topValue)
    | LESS (e1, e2) -> (match (eval (mem, e1), eval (mem, e2)) with
                        | ((BOT_ITV, _), (_, _)) -> botValue
                        | ((_, _), (BOT_ITV, _)) -> botValue
                        | ((ITV (Z p1, Z q1), _), (ITV (Z p2, Z q2), _)) -> if q1 < p2 then (BOT_ITV, T) else if p1 >= q2 then (BOT_ITV, F) else (BOT_ITV, TOP_BOOL)
                        | ((ITV (_, Z q1), _), (ITV (Z p2, _), _)) -> if q1 < p2 then (BOT_ITV, T) else (BOT_ITV, TOP_BOOL)
                        | ((ITV (_, _), _), (ITV (_, _), _)) -> (BOT_ITV, TOP_BOOL)
                        | _ -> topValue)
    | _ -> topValue

  (* memory filtering by boolean expression *)
  let rec assume : (memory * exp) -> memory = fun (mem, e) ->
      match e with
      | TRUE -> mem
      | FALSE -> botMemory
	  | VAR id -> (match mem id with
                   | (_, TOP_BOOL) -> mem
                   | (_, T) -> mem
                   | (_, F) -> botMemory
                   | (_, BOT_BOOL) -> botMemory
                   | _ -> topMemory) 
      | ANDALSO (e1, e2) -> assume (assume (mem, e1), e2)
      | ORELSE (e1, e2) -> join_memory (assume (mem, e1), assume (assumeNot (mem, e1), e2)) (used_vars_exp e)
      | NOT e -> assumeNot (mem, e)
      | LESS (VAR x, NUM n) -> (match eval (mem, VAR x) with
                                | (BOT_ITV, _) -> botMemory
                                | (ITV (Z p, Z q), _) -> if p < n then store mem x (ITV (Z p, Z (min q (n-1))), BOT_BOOL) else botMemory
                                | (ITV (Z p, MAX), _) -> if p < n then store mem x (ITV (Z p, Z (n-1)), BOT_BOOL) else botMemory
                                | (ITV (MIN, Z q), _) -> store mem x (ITV (MIN, Z (min q (n-1))), BOT_BOOL)
                                | (ITV (MIN, MAX), _) -> store mem x (ITV (MIN, Z (n-1)), BOT_BOOL)
                                | _ -> topMemory)
      | LESS (NUM n, VAR x) -> (match eval (mem, VAR x) with
                                | (BOT_ITV, _) -> botMemory
                                | (ITV (Z p, Z q), _) -> if n < q then store mem x (ITV (Z (max p (n+1)), Z q), BOT_BOOL) else botMemory
                                | (ITV (MIN, Z q), _) -> if n < q then store mem x (ITV (Z (n+1), Z q), BOT_BOOL) else botMemory
                                | (ITV (Z p, MAX), _) -> store mem x (ITV (Z (max p (n+1)), MAX), BOT_BOOL)
                                | (ITV (MIN, MAX), _) -> store mem x (ITV (Z (n+1), MAX), BOT_BOOL)
                                | _ -> topMemory)
      | LESS (_, _) -> topMemory
	  | _ -> botMemory

  and assumeNot : (memory * exp) -> memory = fun (mem, e) ->
      match e with
      | TRUE -> botMemory
      | FALSE -> mem 
	  | VAR id -> (match mem id with
                   | (_, TOP_BOOL) -> mem
                   | (_, F) -> mem
                   | (_, T) -> botMemory
                   | (_, BOT_BOOL) -> botMemory
                   | _ -> topMemory) 
      | ANDALSO (e1, e2) -> join_memory (assumeNot (mem, e1), assumeNot (assume (mem, e1), e2)) (used_vars_exp e) 
      | ORELSE (e1, e2) -> assumeNot (assumeNot (mem, e1), e2)
      | NOT e -> assume (mem, e)
      | LESS (VAR x, NUM n) -> (match eval (mem, VAR x) with
                                | (BOT_ITV, _) -> botMemory
                                | (ITV (Z p, Z q), _) -> if n <= q then store mem x (ITV (Z p, Z (max p n)), BOT_BOOL) else botMemory
                                | (ITV (Z p, MAX), _) -> store mem x (ITV (Z (max p n), MAX), BOT_BOOL)
                                | (ITV (MIN, Z q), _) -> if n <= q then store mem x (ITV (Z n, Z q), BOT_BOOL) else botMemory
                                | (ITV (MIN, MAX), _) -> store mem x (ITV (Z n, MAX), BOT_BOOL)
                                | _ -> topMemory)
      | LESS (NUM n, VAR x) -> (match eval (mem, VAR x) with
                                | (BOT_ITV, _) -> botMemory
                                | (ITV (Z p, Z q), _) -> if p <= n then store mem x (ITV (Z p, Z (min n q)), BOT_BOOL) else botMemory
                                | (ITV (MIN, Z q), _) -> store mem x (ITV (MIN, Z (min n q)), BOT_BOOL)
                                | (ITV (Z p, MAX), _) -> if p <= n then store mem x (ITV (Z p, Z n), BOT_BOOL) else botMemory
                                | (ITV (MIN, MAX), _) -> store mem x (ITV (MIN, Z n), BOT_BOOL)
                                | _ -> topMemory)
      | LESS (_, _) -> topMemory
	  | _ -> botMemory

  (* interval analysis for K- *)
  let rec analyzer : (memory * program) -> memory = fun (mem, pgm) ->
    let varlist = used_varlist pgm in
	match pgm with
	| SKIP -> mem
	| ASSIGN(id, e) -> store mem id (eval (mem, e))
    | SEQ(cmd1, cmd2) -> let mem1 = analyzer (mem, cmd1) in analyzer (mem1, cmd2) 
    | IF(e, cmd1, cmd2) -> join_memory (analyzer(assume(mem, e), cmd1), analyzer(assumeNot(mem, e), cmd2)) varlist
	| WHILE(e, cmd) -> let ftn = (fun x -> join_memory (mem, analyzer(assume(x, e), cmd)) varlist) in assumeNot((narrow (widen ftn varlist) ftn varlist), e)
end
