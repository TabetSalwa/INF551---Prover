(** 1  Type inference for a simply typed calculus **)

type tvar = string
type var = string

(* 1.1  Simple types *)

type ty =
  |Tvar of tvar
  |Imp of ty*ty
  |And of ty*ty
  |True
  |Or of ty*ty
  |False
  |Nat

(* 1.2  lambda-terms *)

type tm =
  |Var of var
  |Abs of var*ty*tm
  |App of tm*tm
  |Pair of tm*tm
  |Fst of tm
  |Snd of tm
  |Unit
  |Left of tm*ty
  |Right of ty*tm
  |Case of tm*var*tm*var*tm
  |Absurd of tm*ty
  |Zero
  |Succ of tm
  |Rec of tm*tm*var*var*tm

(* 1.3  String representation *)

let string_of_ty =
  let rec arr = function
    |Imp (t1,t2) -> (sum t1)^" => "^(arr t2)
    |x -> sum x
  and sum = function
    |Imp (t1,t2) -> "("^(sum t1)^" => "^(arr t2)^")"
    |Or (t1,t2) -> (prod t1)^" \u{2228} "^(sum t2)
    |x -> prod x
  and prod = function
    |Imp (t1,t2) -> "("^(sum t1)^" => "^(arr t2)^")"
    |Or (t1,t2) -> "("^(prod t1)^" \u{2228} "^(sum t2)^")"
    |And (t1,t2) -> (base t1)^" \u{2227} "^(prod t2)
    |x -> base x
  and base = function
    |Imp (t1,t2) -> "("^(sum t1)^" => "^(arr t2)^")"
    |Or (t1,t2) -> "("^(prod t1)^" \u{2228} "^(sum t2)^")"
    |And (t1,t2) -> "("^(base t1)^" \u{2227} "^(prod t2)^")"
    |Tvar s -> s
    |True -> "\u{22a4}"
    |False -> "\u{22a5}"
    |Nat -> "\u{2115}"
  in arr

let rec string_of_tm =
  let rec abs = function
    |Abs (x,t,tm) -> "\u{03bb}("^x^" : "^(string_of_ty t)^") \u{2192} "^(abs tm)
    |Pair (t1,t2) -> "("^(abs t1)^" , "^(abs t2)^")"
    |Left (t,ty) -> "\u{03b9}\u{2081}("^(abs t)^" , "^(string_of_ty ty)^")"
    |Right (ty,t) -> "\u{03b9}\u{2082}("^(string_of_ty ty)^" , "^(abs t)^")"
    |Case (t,x,u,y,v) -> "case("^(abs t)^" , "^x^" \u{21a6} "^(abs u)^" , "^y^" \u{21a6} "^(abs v)^")"
    |Absurd (t,_) -> "case("^(abs t)^")"
    |App (t1,t2) -> (base t1)^" "^(base t2)
    |Fst t -> "\u{03c0}\u{2081}"^(base t)
    |Snd t -> "\u{03c0}\u{2082}"^(base t)
    |Unit -> "()"
    |Zero -> "0"
    |Succ t -> "succ("^(abs t)^")"
    |Rec (n,z,k,a,t) -> "rec("^(abs n)^" , "^(abs z)^" , "^k^" "^a^" \u{21a6} "^(abs t)^")"
    |Var x -> x
  and base = function
    |Abs (x,t,tm) -> "(\u{03bb}("^x^" : "^(string_of_ty t)^") \u{2192} "^(abs tm)^")"
    |Pair (t1,t2) -> "("^(abs t1)^" , "^(abs t2)^")"
    |Left (t,ty) -> "(\u{03b9}\u{2081}("^(abs t)^" , "^(string_of_ty ty)^"))"
    |Right (ty,t) -> "(\u{03b9}\u{2082}("^(string_of_ty ty)^" , "^(abs t)^"))"
    |Case (t,x,u,y,v) -> "(case("^(abs t)^" , "^x^" \u{21a6} "^(abs u)^" , "^y^" \u{21a6} "^(abs v)^"))"
    |Absurd (t,_) -> "(case("^(abs t)^"))"
    |App (t1,t2) -> "("^(abs t1)^" "^(base t2)^")"
    |Fst t -> "(\u{03c0}\u{2081}"^(base t)^")"
    |Snd t -> "(\u{03c0}\u{2082}"^(base t)^")"
    |Unit -> "()"
    |Zero -> "0"
    |Succ t -> "(succ("^(abs t)^"))"
    |Rec (n,z,k,a,t) -> "(rec("^(abs n)^" , "^(abs z)^" , "^k^" "^a^" \u{21a6} "^(abs t)^"))"
    |Var x -> x
  in abs

let () = assert (let test = Abs ("f",Imp (Tvar "A",Tvar "B"),Abs ("x",Tvar "A",App (Var "f",Var "x"))) in string_of_tm test = "\u{03bb} (f : A => B) \u{2192} \u{03bb} (x : A) \u{2192} f x")

(* 1.6  Type inference and checking together *)

exception Type_error

let rec infer_type ctx = function
  |Var x -> (try List.assoc x ctx with Not_found -> raise Type_error)
  |Abs (x,t,tm) -> Imp (t,(infer_type ((x,t)::ctx) tm))
  |App (t1,t2) -> (match infer_type ctx t1 with
    |Imp (u,v) -> if check_type ctx t2 u then v else raise Type_error
    |_ -> raise Type_error)
  |Pair (t1,t2) -> And (infer_type ctx t1,infer_type ctx t2)
  |Fst t -> (match infer_type ctx t with And (u,_) -> u |_ -> raise Type_error)
  |Snd t -> (match infer_type ctx t with And (_,v) -> v |_ -> raise Type_error)
  |Unit -> True
  |Left (t,ty) -> Or (infer_type ctx t,ty)
  |Right (ty,t) -> Or (ty,infer_type ctx t)
  |Case (t,x,u,y,v) -> (match infer_type ctx t with
    |Or (t1,t2) -> let ty = infer_type ((x,t1)::ctx) u in if ty=(infer_type ((y,t2)::ctx) v) then ty else raise Type_error
    |_ -> raise Type_error)
  |Absurd (t,ty) -> if check_type ctx t False then ty else raise Type_error
  |Zero -> Nat
  |Succ t -> if check_type ctx t Nat then Nat else raise Type_error
  |Rec (n,z,k,a,t) ->
    let ty = infer_type ctx z in
    if (check_type ctx n Nat) && (check_type ((k,Nat)::(a,ty)::ctx) t ty) then ty else raise Type_error
and check_type ctx t ty = match t,ty with
  |Var x,_ -> List.mem (x,ty) ctx
  |Abs (x,t,tm),Imp (u,v) -> (u=t) && (check_type ((x,t)::ctx) tm v)
  |App (t1,t2),_ -> check_type ctx t1 (Imp (infer_type ctx t2,ty))
  |Pair (t1,t2),And (ty1,ty2) -> (check_type ctx t1 ty1) && (check_type ctx t2 ty2)
  |Fst t,_ -> (match infer_type ctx t with And (ty',_) -> ty=ty'|_ -> false)
  |Snd t,_ -> (match infer_type ctx t with And (_,ty') -> ty=ty'|_ -> false)
  |Unit,True -> true
  |Left (t,ty'),Or (ty1,ty2) -> (check_type ctx t ty1) && (ty'=ty2)
  |Right (ty',t),Or (ty1,ty2) -> (check_type ctx t ty2) && (ty'=ty1)
  |Case (t,x,u,y,v),_ -> (match infer_type ctx t with
    |Or (t1,t2) -> (check_type ((x,t1)::ctx) u ty) && (check_type ((y,t2)::ctx) v ty)
    |_ -> false)
  |Absurd (t,ty'),_ -> (check_type ctx t False) && (ty=ty')
  |Zero,Nat -> true
  |Succ t,Nat -> check_type ctx t Nat
  |Rec (n,z,k,a,t),ty ->
    (check_type ctx n Nat) && (check_type ctx z ty) && (check_type ((k,Nat)::(a,ty)::ctx) t ty)
  |_ -> false

let () = assert (let test = Abs ("f",Imp (Tvar "A",Tvar "B"),Abs ("g",Imp (Tvar "B",Tvar "C"),Abs ("x",Tvar "A",App (Var "g",App (Var "f",Var "x"))))) in (infer_type [] test)=(Imp (Imp (Tvar "A",Tvar "B"),Imp (Imp (Tvar "B",Tvar "C"),Imp (Tvar "A",Tvar "C")))))
let () = assert (let test = Abs ("f",Tvar "A",Var "x") in try let _ = infer_type [] test in false with Type_error -> true)
let () = assert (let test = Abs ("f",Tvar "A",Abs ("x",Tvar "B",App (Var "f",Var "x"))) in try let _ = infer_type [] test in false with Type_error -> true)
let () = assert (let test = Abs ("f",Imp (Tvar "A",Tvar "B"),Abs ("x",Tvar "B",App (Var "f",Var "x"))) in try let _ = infer_type [] test in false with Type_error -> true)
let () = assert (let test = Abs ("x",Tvar "A",Var "x") in check_type [] test (Imp (Tvar "A",Tvar "A")))
let () = assert (let test = Abs ("x",Tvar "A",Var "x") in not (check_type [] test (Imp (Tvar "B",Tvar "B"))))
let () = assert (let test = Var "x" in not (check_type [] test (Tvar "A")))

(* 1.7  Other connectives *)

(* 1.8  Conjunction *)

let and_comm = Abs ("x",And (Tvar "A",Tvar "B"),Pair (Snd (Var "x"),Fst (Var "x")))

let () = assert (check_type [] and_comm (Imp (And (Tvar "A",Tvar "B"),And (Tvar "B",Tvar "A"))))

(* 1.9  Truth *)

let true_simpl = Abs ("x",Imp (True,Tvar "A"),App (Var "x",Unit))

let () = assert (check_type [] true_simpl (Imp (Imp (True,Tvar "A"),Tvar "A")))

(* 1.10  Disjunction *)

let or_comm = Abs ("x",Or (Tvar "A",Tvar "B"),Case (Var "x","y",Right (Tvar "B",Var "y"),"y",Left (Var "y",Tvar "A")))

let () = assert (check_type [] or_comm (Imp (Or (Tvar "A",Tvar "B"),Or (Tvar "B",Tvar "A"))))

(* 1.11  Falsity *)

let contradiction = Abs ("x",And (Tvar "A",Imp (Tvar "A",False)),Absurd (App (Snd (Var "x"),Fst (Var "x")),Tvar "B"))

let () = assert (check_type [] contradiction (Imp (And (Tvar "A",Imp (Tvar "A",False)),Tvar "B")))

(* 1.12  Parsing strings *)

let () = Printexc.record_backtrace true
exception Parse_error
let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () |_ -> raise Parse_error
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true |_ -> false
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
let ident s = match Stream.next s with Genlex.Ident x -> x |_ -> raise Parse_error
let lexer = Genlex.make_lexer ["(";")";"=>";"=>";"/\\";"\\/";"fun";"->";",";":";"fst";"snd";"T";"left";"right";"not";"case";"of";"|";"absurd";"_";"Nat";"succ";"rec";"0"]
let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = sum () in
    if peek_kwd s "=>" then Imp (a,arr ()) else a
  and sum () =
    let a = prod () in
    if peek_kwd s "\\/" then Or (a,sum ()) else a
  and prod () =
    let a = base () in
    if peek_kwd s "/\\" then And (a,prod ()) else a
  and base () =
    match Stream.next s with
      |Genlex.Ident x -> Tvar x
      |Genlex.Kwd "(" ->
        let a = ty () in
        must_kwd s ")";
        a
      |Genlex.Kwd "T" -> True
      |Genlex.Kwd "_" -> False
      |Genlex.Kwd "not" ->
        let a = base () in
        Imp (a,False)
      |Genlex.Kwd "Nat" -> Nat
      |_ -> raise Parse_error
  in ty ()
let tm_of_tk s =
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")";",";"case";"fun";"of";"->";"|"] in
  let ty () = ty_of_tk s in
  let rec tm () = app ()
  and app () =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t,abs())
    done;
    !t
  and abs () =
    if peek_kwd s "fun" then
      begin
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x,a,t)
      end
    else if peek_kwd s "case" then
      begin
        let t = tm () in
        must_kwd s "of";
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t,x,u,y,v)
      end
    else
      base ()
  and base () =
    match Stream.next s with
      |Genlex.Ident x -> Var x
      |Genlex.Kwd "0" -> Zero
      |Genlex.Kwd "(" ->
        if peek_kwd s ")" then
          Unit
        else
          let t = tm () in
          if peek_kwd s "," then
            let u = tm () in
            must_kwd s ")";
            Pair (t,u)
          else
            begin
              must_kwd s ")";
              t
            end
      |Genlex.Kwd "fst" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ")";
        Fst t
      |Genlex.Kwd "snd" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ")";
        Snd t
      |Genlex.Kwd "left" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ",";
        let b = ty () in
        must_kwd s ")";
        Left (t,b)
      |Genlex.Kwd "right" ->
        must_kwd s "(";
        let a = ty () in
        must_kwd s ",";
        let t = tm () in
        must_kwd s ")";
        Right (a,t)
      |Genlex.Kwd "absurd" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ",";
        let a = ty () in
        must_kwd s ")";
        Absurd (t,a)
      |Genlex.Kwd "succ" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ")";
        Succ t
      |Genlex.Kwd "rec" ->
        must_kwd s "(";
        let n = tm () in
        must_kwd s ",";
        let z = tm () in
        must_kwd s ",";
        let x = ident s in
        let y = ident s in
        must_kwd s "->";
        let s = tm () in
        Rec (n,z,x,y,s)
      |_ -> raise Parse_error
  in
  tm ()
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))

(* (* Parsing tests *)

let () =
  let l = [
      "A => B";
      "A /\\ B";
      "T";
      "A \\/ B";
      "_";
      "not A"
    ]
  in
  List.iter (fun s -> Printf.printf "The parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l

let () =
  let l = [
      "t u";
      "fun (x : A) -> t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
    ]
  in
  List.iter (fun s -> Printf.printf "The parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l
*)


(** 2  Interactive prover **)

(* 2.1  String representation of contexts *)

type context = (string*ty) list

let string_of_ctx ctx = String.concat " , " (List.rev_map (fun (x,ty) -> x^" : "^(string_of_ty ty)) ctx)

(* 2.2  Sequents *)

type sequent = context*ty

let string_of_seq (ctx,ty) = (string_of_ctx ctx)^" \u{22a2} "^(string_of_ty ty)

(* 2.3  An interactive prover *)

type channel =
  |In of in_channel*string
  |Out of out_channel
  |No

let read chan = match chan with
  |In (chan_in,filename) -> (try let s = input_line chan_in in print_endline s; s,chan with End_of_file -> input_line stdin,Out (open_out_gen [Open_append] 0 filename))
  |_ -> input_line stdin,chan

let write chan s = match chan with
  |Out chan_out -> output_string chan_out (s^"\n"); chan
  |_ -> chan

let rec prove chan env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error chan e = print_endline e; prove chan env a in
  let command,chan = read chan in
  let cmd,arg =
    let n = try String.index command ' ' with Not_found -> String.length command in
    let c = String.sub command 0 n in
    let a = String.sub command n (String.length command - n) in
    let a = String.trim a in
    c,a
  in
  match cmd with
    |"intro" ->
      begin
        match a with
          |Imp (a,b) ->
            if arg = "" then error chan "Please provide an argument for intro." else
            let chan = write chan command in
            let t,chan = prove chan ((arg,a)::env) b in
            Abs (arg,a,t),chan
          |And (a,b) ->
            if arg <> "" then error chan "Please don't provide an argument for intro." else
            let chan = write chan command in
            let t1,chan = prove chan env a in
            let t2,chan = prove chan env b in
            Pair (t1,t2),chan
          |True ->
            if arg <> "" then error chan "Please don't provide an argument for intro." else
            let chan = write chan command in
            Unit,chan
          |Nat ->
            if arg = "zero" then
              let chan = write chan command in
              Zero,chan
            else if arg = "succ" then
              let chan = write chan command in
              let t,chan = prove chan env Nat in
              Succ t,chan
            else error chan "Please provide an option for intro (\"zero\" or \"succ\")."
          |_ -> error chan "Don't know how to introduce this."
      end
    |"elim" ->
      let arg1,arg2 =
        let n = try String.index arg ' ' with Not_found -> String.length arg in
        let a1 = String.sub arg 0 n in
        let a2 = String.sub arg n (String.length arg - n) in
        let a2 = String.trim a2 in
        a1,a2
      in
      if arg1 = "" then error chan "Please provide an argument for elim." else
      begin
        try match List.assoc arg1 env with
          |Imp (u,v) ->
            if arg2 <> "" then error chan "Please provide one argument only for elim." else
            if v=a then
              let chan = write chan command in
              let t,chan = prove chan env u in
              App (Var arg,t),chan
            else error chan "Not the right type."
          |Or (u,v) ->
            if arg2 <> "" then error chan "Please provide one argument only for elim." else
            let chan = write chan command in
            let t1,chan = prove chan ((arg1,u)::env) a in
            let t2,chan = prove chan ((arg1,v)::env) a in
            Case (Var arg1,arg1,t1,arg1,t2),chan
          |False ->
            if arg2 <> "" then error chan "Please provide one argument only for elim." else
            let chan = write chan command in
            Absurd (Var arg1,a),chan
          |Nat ->
            if arg2 = "" then error chan "Please provide a second argument for elim." else
            begin
              try
                let b = List.assoc arg2 env in
                if b=a then
                  let chan = write chan command in
                  let t,chan = prove chan env a in
                  Rec (Var arg1,Var arg2,arg1,arg2,t),chan
                else error chan ("Variable "^arg2^"does not have the right type.")
              with Not_found -> error chan ("Variable "^arg2^" not found.")
            end
          |_ -> error chan "Don't know how to eliminate this."
        with Not_found -> error chan ("Variable "^arg1^" not found.")
      end
    |"cut" ->
      begin
        try
          let b = ty_of_string arg in
          let chan = write chan command in
          let t1,chan = prove chan env (Imp (b,a)) in
          let t2,chan = prove chan env b in
          App (t1,t2),chan
        with Parse_error -> error chan "cut expects a type as an argument."
      end
    |"exact" ->
      begin
        try
          let t = tm_of_string arg in
          if infer_type env t <> a then error chan "Not the right type."
          else let chan = write chan command in t,chan
        with Parse_error -> error chan "exact expects a \u{03bb}-term as an argument."
      end
    |"fst" ->
      if arg = "" then error chan "Please provide an argument for fst." else
      begin
        try
          match List.assoc arg env with
          |And (u,_) ->
            if a=u then
              let chan = write chan command in
              Fst (Var arg),chan
            else error chan "Not the right type."
          |_ -> error chan "Not the right type."
        with Not_found -> error chan ("Variable "^arg^" not found.")
      end
    |"snd" ->
      if arg = "" then error chan "Please provide an argument for snd." else
      begin
        try
          match List.assoc arg env with
          |And (_,v) ->
            if a=v then
              let chan = write chan command in
              Snd (Var arg),chan
            else error chan "Not the right type."
          |_ -> error chan "Not the right type."
        with Not_found -> error chan ("Variable "^arg^" not found.")
      end
    |"left" ->
      if arg <> "" then error chan "left does not require an argument" else
      begin
        match a with
        |Or (a,b) ->
          let chan = write chan command in
          let t,chan = prove chan env a in
          Left (t,b),chan
        |_ -> error chan "Target type is not a disjunction."
      end
    |"right" ->
      if arg <> "" then error chan "right does not require an argument" else
      begin
        match a with
        |Or (a,b) ->
          let chan = write chan command in
          let t,chan = prove chan env b in
          Right (a,t),chan
        |_ -> error chan "Target type is not a disjunction."
      end
    |_ -> error chan ("Unknown command: "^cmd)

let () =
  let filename = ref "" in
  Arg.parse [] (fun s -> filename := s) "";
  let chan = if !filename = "" then No else try In (open_in ("Proofs/"^ !filename),"Proofs/"^ !filename) with Sys_error _ -> Out (open_out ("Proofs/"^ !filename)) in
  print_endline "Please enter the formula to prove:";
  let a,chan = read chan in
  let chan = write chan a in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t,_ = prove chan [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking...";
  flush_all ();
  assert (check_type [] t a);
  print_endline "ok."
