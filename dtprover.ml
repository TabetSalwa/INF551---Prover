(** 5  Dependent types **)

(* 5.1  Expressions *)

type var = string

type expr =
  |Type
  |Var of var
  |App of expr*expr
  |Abs of var*expr*expr
  |Pi of var*expr*expr
  |Nat
  |Z
  |S of expr
  |Ind of expr*expr*expr*expr
  |Eq of expr*expr
  |Refl of expr
  |J of expr*expr*expr*expr*expr

(* 5.2  String representation *)

let to_string =
  let rec abs = function
    |Type -> "Type"
    |Var x -> x
    |App (t1,t2) -> (abs t1)^" "^(base t2)
    |Abs (x,ty,tm) -> "\u{03bb}("^x^" : "^(abs ty)^") \u{2192} "^(abs tm)
    |Pi (x,a,b) -> "\u{03a0}("^x^" : "^(abs a)^") \u{2192}  "^(abs b)
    |Nat -> "\u{2115}"
    |Z -> "Z"
    |S t -> "S "^(base t)
    |Ind (p,z,s,n) -> "Ind "^(base p)^" "^(base z)^" "^(base s)^" "^(base n)
    |Eq (t,u) -> "Eq "^(base t)^" "^(base u)
    |Refl t -> "Refl "^(base t)
    |J (p,r,x,y,e) -> "J "^(base p)^" "^(base r)^" "^(base x)^" "^(base y)^" "^(base e)
  and base = function
    |Type -> "(Type)"
    |Var x -> x
    |App (t1,t2) -> "("^(abs t1)^" "^(base t2)^")"
    |Abs (x,ty,tm) -> "(\u{03bb}("^x^" : "^(abs ty)^") \u{2192} "^(abs tm)^")"
    |Pi (x,a,b) -> "(\u{03a0}("^x^" : "^(abs a)^") \u{2192} "^(abs b)^")"
    |Nat -> "\u{2115}"
    |Z -> "Z"
    |S t -> "(S "^(base t)^")"
    |Ind (p,z,s,n) -> "(Ind "^(base p)^" "^(base z)^" "^(base s)^" "^(base n)^")"
    |Eq (t,u) -> "(Eq "^(base t)^" "^(base u)^")"
    |Refl t -> "(Refl "^(base t)^")"
    |J (p,r,x,y,e) -> "(J "^(base p)^" "^(base r)^" "^(base x)^" "^(base y)^" "^(base e)^")"
  in abs

(* 5.3  Fresh variable names *)

let fresh_var =
  let r = ref 0 in
  function () -> r := !r+1; "x"^(string_of_int !r)

(* 5.4  Substitution *)

let rec subst x t = function
  |Type -> Type
  |Var y -> if y=x then t else Var y
  |App (t1,t2) -> App (subst x t t1,subst x t t2)
  |Abs (y,ty,tm) -> let z = fresh_var () in Abs (z,subst x t ty, subst x t (subst y (Var z) tm))
  |Pi (y,a,b) -> let z = fresh_var () in Pi (z,subst x t a, subst x t (subst y (Var z) b))
  |Nat -> Nat
  |Z -> Z
  |S tm -> S (subst x t tm)
  |Ind (p,z,s,n) -> Ind (subst x t p,subst x t z,subst x t s, subst x t n)
  |Eq (u,v) -> Eq (subst x t u,subst x t v)
  |Refl u -> Refl (subst x t u)
  |J (p,r,a,b,e) -> J (subst x t p,subst x t r,subst x t a,subst x t b,subst x t e)

(* 5.5  Contexts *)

type context = (var*(expr*expr option)) list

let string_of_context ctx = String.concat "\n" (List.map (fun (x,(ty,v)) -> x^" : "^(to_string ty)^(match v with Some tm -> " = "^(to_string tm) |None -> "")) ctx)

(* 5.6  Normalization *)

let rec normalize ctx = function
  |Type -> Type
  |Var x ->
    begin
      try match snd (List.assoc x ctx) with
        |Some tm -> normalize ctx tm
        |None -> Var x
      with Not_found -> Var x
    end
  |App (t1,t2) ->
    begin
      match normalize ctx t1 with
        |Abs (x,ty,t) ->
          let t2 = normalize ctx t2 in
          normalize ctx (subst x t2 t)
        |t -> App (normalize ctx t,normalize ctx t2)
    end
  |Abs (x,ty,tm) -> let ty = normalize ctx ty in Abs (x,normalize ctx ty,normalize ((x,(ty,None))::ctx) tm)
  |Pi (x,a,b) -> Pi (x,normalize ctx a,normalize ctx b)
  |Nat -> Nat
  |Z -> Z
  |S t -> S (normalize ctx t)
  |Ind (p,z,s,n) ->
    begin
      match normalize ctx n with
        |Z -> normalize ctx z
        |S n ->
          let s = normalize ctx s in
          normalize ctx (App (App (s,n),Ind (normalize ctx p,normalize ctx z,s,n)))
        |n -> Ind (normalize ctx p,normalize ctx z,normalize ctx s,n)
    end
  |Eq (t,u) -> Eq (normalize ctx t,normalize ctx u)
  |Refl t -> Refl (normalize ctx t)
  |J (p,r,x,y,e) ->
    begin
      match normalize ctx e with
        |Refl a when x=a && y=a -> normalize ctx (App (r,a))
        |e -> J (normalize ctx p,normalize ctx r,normalize ctx x,normalize ctx y,e)
    end

(* 5.7  alpha-conversion *)

(* For this question, instead of using substitution, I stored the correspondences between variables in a 'context' of type (var*var) list
In order for two variables x and y to be alpha-equivalent in a context, the latest abstraction bounding x must correspond to a bounding of y, and vice versa. The function corresp implements this *)

let alpha =
  let rec conv ctx t1 t2 = match t1,t2 with
    |Type,Type -> true
    |Var x,Var y ->
      let rec corresp x y = function
        |[] -> x=y
        |(a,b)::t -> if a=x then b=y else (b <> y && corresp x y t)
      in corresp x y ctx
    |App (u1,u2),App (v1,v2) -> conv ctx u1 v1 && conv ctx u2 v2
    |Abs (x,ty1,t1),Abs (y,ty2,t2) -> conv ctx ty1 ty2 && conv ((x,y)::ctx) t1 t2
    |Pi (x,a1,b1),Pi(y,a2,b2) -> conv ctx a1 a2 && conv ((x,y)::ctx) b1 b2
    |Nat,Nat -> true
    |Z,Z -> true
    |S t1,S t2 -> (conv ctx t1 t2)
    |Ind (p1,z1,s1,n1),Ind (p2,z2,s2,n2) -> (conv ctx p1 p2) && (conv ctx z1 z2) && (conv ctx s1 s2) && (conv ctx n1 n2)
    |Eq (t1,u1),Eq (t2,u2) -> (conv ctx t1 t2) && (conv ctx u1 u2)
    |Refl t1,Refl t2 -> conv ctx t1 t2
    |J (p1,r1,x1,y1,e1),J (p2,r2,x2,y2,e2) -> (conv ctx p1 p2) && (conv ctx r1 r2) && (conv ctx x1 x2) && (conv ctx y1 y2) && (conv ctx e1 e2)
    |_ -> false
  in conv []

(* 5.8  Conversion *)

let conv ctx t1 t2 = alpha (normalize ctx t1) (normalize ctx t2)

(* 5.9  Type inference *)

exception Type_error

let rec infer ctx = function
  |Type -> Type
  |Var x -> (try fst (List.assoc x ctx) with Not_found -> raise Type_error)
  |App (t1,t2) ->
    begin
      let u = infer ctx t2 in
      match infer ctx t1 with
        |Pi (x,a,b) ->
          if conv ctx a u then
            subst x t2 b
          else
            raise Type_error
        |_ -> raise Type_error
    end
  |Abs (x,ty,tm) -> Pi (x,ty,infer ((x,(ty,None))::ctx) tm)
  |Pi _ -> Type
  |Nat -> Type
  |Z -> Nat
  |S t -> if conv ctx (infer ctx t) Nat then Nat else raise Type_error
  |Ind (p,z,s,n) -> normalize ctx (App (p,n))
  |Eq (_,_) -> Type
  |Refl t -> Eq (t,t)
  |J (p,r,x,y,e) -> normalize ctx (App (App (App (p,x),y),e))

(* 5.10  Type checking *)

let check ctx tm ty = if not (conv ctx (infer ctx tm) ty) then raise Type_error

(* 5.11  Interaction loop *)

let () = Printexc.record_backtrace true
exception Parse_error
let lexer = Genlex.make_lexer ["(";",";")";"->";"=>";"fun";"Pi";":";"Type";"Nat";"Z";"S";"Ind";"Eq";"Refl";"J"]
let of_tk s =
  let must_kwd s k = match Stream.next s with
    |Genlex.Kwd k' when k' = k -> ()
    |_ -> raise Parse_error
  in
  let peek_kwd s k = match Stream.peek s with
    |Some (Genlex.Kwd k') when k'=k -> let _ = Stream.next s in true
    |_ -> false
  in
  let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false in
  let ident s = match Stream.next s with
    |Genlex.Ident x -> x
    |_ -> raise Parse_error
  in
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")";"->";"=>";"fun";"Pi";":";"Type"] in
  let rec e () = abs ()
  and abs () =
    if peek_kwd s "Pi" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let b = e () in
        Pi (x,a,b)
      )
    else if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = e () in
        must_kwd s ")";
        must_kwd s "->";
        let t = e () in
        Abs (x,a,t)
      )
    else
      app ()
  and app () =
    let t = ref (arr ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t,base ())
    done;
    !t
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_",t,u)
    else
      t
  and base () =
    match Stream.next s with
      |Genlex.Ident x -> Var x
      |Genlex.Kwd "Type" -> Type
      |Genlex.Kwd "Nat" -> Nat
      |Genlex.Kwd "Z" -> Z
      |Genlex.Kwd "S" ->
        let t = base () in
        S t
      |Genlex.Kwd "Ind" ->
        let p = base () in
        let z = base () in
        let ps = base () in
        let n = base () in
        Ind (p,z,ps,n)
      |Genlex.Kwd "Eq" ->
        let t = base () in
        let u = base () in
        Eq (t,u)
      |Genlex.Kwd "Refl" ->
        let t = base () in
        Refl t
      |Genlex.Kwd "J" ->
        let p = base () in
        let r = base () in
        let x = base () in
        let y = base () in
        let e = base () in
        J (p,r,x,y,e)
      |Genlex.Kwd "(" ->
        let t = e () in
        must_kwd s ")";
        t
      |_ -> raise Parse_error
  in
  e ()
let of_string a = of_tk (lexer (Stream.of_string a))

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s,""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd,arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
        |"assume" ->
          let x,sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x,(a,None)) :: !env;
          print_endline (x^" assumed of type "^(to_string a))
        |"define" ->
          let x,st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x,(a,Some t)) :: !env;
          print_endline (x^" defined to "^(to_string t)^" of type "^(to_string a))
        |"context" ->
          print_endline (string_of_context !env)
        |"type" ->
          let t = of_string arg in
          let a = infer !env t in
          print_endline ((to_string t)^" is of type "^(to_string a))
        |"check" ->
          let t,a = split '=' arg in
          let t = of_string t in
          let a = of_string a in
          check !env t a;
          print_endline "Ok."
        |"eval" ->
          let t = of_string arg in
          let _ = infer !env t in
          print_endline (to_string (normalize !env t))
        |"exit" ->  loop := false
        |"" |"#" -> ()
        |_ -> print_endline ("Unknown command:"^cmd)
    with
      |End_of_file -> loop := false
      |Failure err -> print_endline ("Error: "^err)
      |e -> print_endline ("Error: "^(Printexc.to_string e))
  done;
  print_endline "Bye."

(* 5.12  Natural numbers *)

(* 5.13  Equality *)

(* 5.14  Using the prover *)

(* 5.15  Optional: inductive types *)

(* 5.16  Optional: interactive prover *)

(* 5.17  Optional: universes *)

(* 5.18  Optional: better handling of indices *)
