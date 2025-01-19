open Core
open Binaryer
module Source = Lang.Fabric

let sum = List.fold_left ~init:0 ~f:( + )

let size : Source.Repr.t -> int =
  let size_atom : Source.Repr.atom -> int = function
    | Int32 -> 4
    | Float64 -> 8
    | Box -> failwith "size of Box"
  in
  function
  | Unknown -> failwith "value/type with unknown representation"
  | Atoms ts -> List.map ~f:size_atom ts |> sum

let repr : Source.Repr.t -> T.Type.t =
  let repr_atom : Source.Repr.atom -> T.Type.t = function
    | Int32 -> Type.int32
    | Float64 -> Type.float64
    | Box -> Type.anyref
  in
  function
  | Unknown -> failwith "value/type with unknown representation"
  | Atoms ts -> List.map ~f:repr_atom ts |> Type.cat

let source_type_repr : Source.Type.t -> T.Type.t =
  Fn.compose repr Source.Type.repr

let source_expr_repr : Source.Expr.t -> T.Type.t =
  Fn.compose source_type_repr Source.Expr.type_expr

let source_pattern_repr : Source.Expr.pattern -> T.Type.t =
  Fn.compose source_type_repr Source.Expr.type_pattern

type env = (string, Cell.t) List.Assoc.t
type func = { upvars_t : Cell.struct_t; name : string }

let closure_fun_t (module Ctx : Context) =
  Type.(function_ (cat [ anyref; structref ]) anyref |> of_heap_type)

let closure_t (module Ctx : Context) =
  Ctx.Struct.(
    t
      Type.
        [
          ("fun", field (closure_fun_t (module Ctx)));
          ("upvars", field structref);
        ])

let assemble_expr (module Ctx : Context) ~functions =
  let open Ctx in
  let unit_t = Struct.(t []) in
  let ret_unit e = Control.block [ e; Struct.make unit_t [] ] in
  let int_t = Struct.(t [ ("value", Type.(field int32)) ]) in
  let tuple_t k =
    Struct.t (List.init k ~f:(fun i -> (string_of_int i, Type.(field anyref))))
  in
  let array_t = Array.t Type.(field ~mut:true anyref) in
  let record_labels_t = Array.t Type.(field int32) in
  let record_values_t = Array.t Type.(field anyref) in
  let record_t =
    let open Type in
    Struct.t
      [
        ("labels", field (record_labels_t.array_type |> of_heap_type));
        ("values", field (record_values_t.array_type |> of_heap_type));
      ]
  in
  let closure_fun_t = closure_fun_t (module Ctx) in
  let closure_t = closure_t (module Ctx) in
  let wrap_int e = Struct.(make int_t [ ("value", e) ]) in
  let unwrap_int e = Cell.( ! ) Struct.(cell int_t e "value") in
  let gensym =
    let cnt = ref 0 in
    fun prefix ->
      cnt := !cnt + 1;
      prefix ^ string_of_int !cnt
  in
  let rec go env (expr : Source.Expr.t) : T.Expression.t =
    let open Source.Expr in
    let ( !! ) x = Cell.( ! ) (List.Assoc.find_exn env ~equal:String.equal x) in
    match expr with
    | Fun (_, _) -> failwith "cannot assemble first-class functions"
    | Var (x, _) -> !!x
    | Lit n -> wrap_int (Const.i32' n)
    | Let (p, e, e') ->
        let v = local (source_pattern_repr p) in
        let rec pat e : Source.Expr.pattern -> (string * Cell0.t * expr) list =
          function
          | Atom (x, t) -> [ (x, local (source_type_repr t), e) ]
          | List ps ->
              let t = tuple_t (List.length ps) in
              List.concat_mapi ps ~f:(fun i ->
                  pat (Struct.cell t e (string_of_int i) |> Cell.( ! )))
        in
        let assigns, env_extras =
          match p with
          | Atom (x, _) -> ([], [ (x, v) ])
          | _ ->
              let cs = pat Cell.(!v) p in
              ( List.map cs ~f:(fun (_, c, e) -> Cell.(c := e)),
                List.map cs ~f:(fun (x, c, _) -> (x, c)) )
        in
        Control.block
          ([ Cell.(v := go env e) ] @ assigns @ [ go (env_extras @ env) e' ])
    | Tuple es ->
        let t = tuple_t (List.length es) in
        Struct.make t (List.mapi es ~f:(fun i e -> (string_of_int i, go env e)))
    | Cons fs ->
        Struct.make record_t
          [
            ( "labels",
              List.map fs ~f:(fun (l, _) -> String.hash l |> Const.i32')
              |> Array.make_of_list record_labels_t );
            ( "values",
              List.map fs ~f:(fun (_, e) -> go env e)
              |> Array.make_of_list record_values_t );
          ]
    | Proj (e, l) ->
        let ty = record_t.struct_type |> Type.of_heap_type in
        let v = local Type.anyref in
        let i = local Type.int32 in
        let target_label = Const.i32' (String.hash l) in
        let curr_label =
          Cell.(
            !(Array.cell record_labels_t !(Struct.cell record_t !v "labels") !i))
        in
        let curr_value =
          Cell.(
            !(Array.cell record_values_t !(Struct.cell record_t !v "values") !i))
        in
        Control.block
          Cell.
            [
              (v := go env e |> fun e -> C.Expression.ref_cast me e ty);
              i := Const.i32' 0;
              Control.block ~name:"done"
                [
                  Control.loop ~in_:"next"
                    (Control.block
                       [
                         Control.break ~name:"done"
                           ~cond:Operator.I32.(curr_label = target_label)
                           ();
                         (i := Operator.I32.(!i + Const.i32' 1));
                         Control.break ~name:"next" ();
                       ]);
                ];
              curr_value;
            ]
    | Array (i_, n_, e_) ->
        let n = local Type.int32 in
        let i = local (Type.of_heap_type int_t.struct_type) in
        let a = local (Type.of_heap_type array_t.array_type) in
        let next = gensym "next" in
        Control.block
          Cell.
            [
              n := unwrap_int (go env n_);
              a := Array.make array_t ~size:!n None;
              i := wrap_int (Const.i32' 0);
              Control.loop ~in_:next
                (Control.block
                   Operator.I32.
                     [
                       Array.cell array_t !a (unwrap_int !i)
                       := go ((i_, i) :: env) e_;
                       i := wrap_int (unwrap_int !i + Const.i32' 1);
                       Control.break ~name:next ~cond:(unwrap_int !i < !n) ();
                     ]);
              C.Expression.ref_cast me !a (Type.of_heap_type array_t.array_type);
            ]
    | Idx (e, e') ->
        Array.cell array_t (go env e) (go env e' |> unwrap_int) |> Cell.( ! )
    | Shape _ -> failwith "unimplemented: Shape"
    | Op (e, "", e') ->
        let a = go env e and a' = go env e' in
        Function.call_ref
          (Struct.cell closure_t a "fun" |> Cell.( ! ))
          [ a'; Struct.cell closure_t a "upvars" |> Cell.( ! ) ]
          Type.anyref
    | Op (e, o, e') ->
        let op =
          match o with
          | "+" -> C.Expression.Operator.I32.add
          | "-" -> C.Expression.Operator.I32.sub
          | "*" -> C.Expression.Operator.I32.mul
          | "/" -> C.Expression.Operator.I32.div_s
          | _ -> raise_s [%message "no op for" (o : string)]
        in
        Operator.binary op (go env e |> unwrap_int) (go env e' |> unwrap_int)
        |> wrap_int
    | Closure (k, fv, _) ->
        let { upvars_t; name } = List.nth_exn functions k in
        Struct.make closure_t
          [
            ("fun", C.Expression.ref_func me name closure_fun_t);
            ( "upvars",
              Struct.make upvars_t (List.map fv ~f:(fun (x, _) -> (x, !!x))) );
          ]
    | Intrinsic ("print_i32", e) ->
        Function.call "print_i32"
          [ Struct.(cell int_t (go env e) "value" |> Cell.( ! )) ]
          Type.none
        |> ret_unit
    | Intrinsic (f, _) -> failwith ("unimplemented: Intrinsic " ^ f)
  in
  go

let%expect_test "assemble_expr" =
  let (module Ctx) = context () in
  let open Ctx in
  feature C.Features.reference_types;
  feature C.Features.gc;
  Function.make ~name:"f" ~params:Type.none ~result:Type.anyref (fun _ ->
      "let x = 3 in let y = 4 in (x * x) + (y * y)" |> Syntax.parse_exn
      |> Compiler.propagate_types
      |> assemble_expr (module Ctx) ~functions:[] [])
  |> Function.export "f";
  print_s [%message (validate () : bool)];
  print ();
  [%expect
    {|
    ("validate ()" true)
    (module
     (type $0 (struct (field i32)))
     (type $1 (func (result anyref)))
     (export "f" (func $f))
     (func $f (type $1) (result anyref)
      (local $0 anyref)
      (local $1 anyref)
      (local.set $0
       (struct.new $0
        (i32.const 3)
       )
      )
      (block (result (ref $0))
       (local.set $1
        (struct.new $0
         (i32.const 4)
        )
       )
       (struct.new $0
        (i32.add
         (struct.get $0 0
          (ref.cast (ref $0)
           (struct.new $0
            (i32.mul
             (struct.get $0 0
              (ref.cast (ref $0)
               (local.get $0)
              )
             )
             (struct.get $0 0
              (ref.cast (ref $0)
               (local.get $0)
              )
             )
            )
           )
          )
         )
         (struct.get $0 0
          (ref.cast (ref $0)
           (struct.new $0
            (i32.mul
             (struct.get $0 0
              (ref.cast (ref $0)
               (local.get $1)
              )
             )
             (struct.get $0 0
              (ref.cast (ref $0)
               (local.get $1)
              )
             )
            )
           )
          )
         )
        )
       )
      )
     )
    )
    |}]

let assemble_function (module Ctx : Context) ~closure ~functions ?name
    (fv, p, e) k =
  let open Ctx in
  match ((p : Source.Expr.pattern), closure) with
  | Atom (x, t), true ->
      Function.make ?name
        ~params:Type.(cat [ source_type_repr t; Type.structref ])
        ~result:(source_expr_repr e)
        (fun args ->
          match args with
          | [ x_arg; closure_arg ] ->
              let { upvars_t; _ } = List.nth_exn functions k in
              let clos =
                List.map fv ~f:(fun (y, _t) ->
                    (y, Struct.cell upvars_t Cell.(!closure_arg) y))
              in
              assemble_expr (module Ctx) ~functions ((x, x_arg) :: clos) e
          | _ -> failwith "unreachable")
  | List [], false ->
      Function.make ?name ~params:Type.none ~result:Type.none (fun _ ->
          assemble_expr (module Ctx) ~functions [] e |> C.Expression.drop me)
  | _ -> raise_s [%message (p : Source.Expr.pattern) (closure : bool)]

let assemble Source.Prog.{ functions; main } : T.Module.t =
  let (module Ctx) = context () in
  let open Ctx in
  feature C.Features.reference_types;
  feature C.Features.gc;
  (* 
  (* Allocations *)
  let top_alloc =
    global "top_alloc" Type.int32 (Const.i32 (Int32.of_int_exn 420))
  in
  Memory.set ~initial:10 ~maximum:10 ();
  *)
  let fs = List.length functions in
  let functions' =
    List.mapi functions ~f:(fun k (fv, _, _) ->
        {
          name = "func" ^ string_of_int k;
          upvars_t =
            Struct.t
              Type.(
                List.map fv ~f:(fun (x, t) -> (x, field (source_type_repr t))));
        })
  in
  List.iteri (List.zip_exn functions functions')
    ~f:(fun k ((fv, p, e), { name; _ }) ->
      assemble_function
        (module Ctx)
        ~closure:true ~functions:functions' ~name (fv, p, e) k
      |> ignore);
  let main =
    assemble_function
      (module Ctx)
      ~closure:false ~functions:functions' ~name:"main" ([], List [], main)
      (fs + 1)
  in
  Function.start main;
  Function.export "main" main;
  (* Import.add_function_import md "print" "spectest" "print" Type.none Type.none; *)
  Function.import "print_i32" "spectest" "print_i32" Type.int32 Type.none;
  me

let%expect_test "assemble" =
  let (module Ctx) =
    Binaryer.context_of_module
      ("let a = 1 in let b = 2 in let f = (x: int => (x*b)+a) in %print_i32 (f \
        3)" |> Syntax.parse_exn |> Compiler.propagate_types
     |> Compiler.lift_lambdas |> assemble)
  in
  let open Ctx in
  let valid = validate () in
  print_s [%message (valid : bool)];
  interpret ();
  print ();
  [%expect
    {|
    (valid true)
    7 : i32
    (module
     (type $0 (struct (field i32)))
     (type $1 (struct (field anyref) (field anyref)))
     (type $2 (struct))
     (type $3 (func (param anyref structref) (result anyref)))
     (type $4 (struct (field (ref $3)) (field structref)))
     (type $5 (func))
     (type $6 (func (param i32)))
     (import "spectest" "print_i32" (func $print_i32 (type $6) (param i32)))
     (elem declare func $func0)
     (export "main" (func $main))
     (start $main)
     (func $func0 (type $3) (param $0 anyref) (param $1 structref) (result anyref)
      (struct.new $0
       (i32.add
        (struct.get $0 0
         (ref.cast (ref $0)
          (struct.new $0
           (i32.mul
            (struct.get $0 0
             (ref.cast (ref $0)
              (local.get $0)
             )
            )
            (struct.get $0 0
             (ref.cast (ref $0)
              (struct.get $1 1
               (ref.cast (ref $1)
                (local.get $1)
               )
              )
             )
            )
           )
          )
         )
        )
        (struct.get $0 0
         (ref.cast (ref $0)
          (struct.get $1 0
           (ref.cast (ref $1)
            (local.get $1)
           )
          )
         )
        )
       )
      )
     )
     (func $main (type $5)
      (local $0 anyref)
      (local $1 anyref)
      (local $2 anyref)
      (drop
       (block (result (ref $2))
        (local.set $0
         (struct.new $0
          (i32.const 1)
         )
        )
        (block (result (ref $2))
         (local.set $1
          (struct.new $0
           (i32.const 2)
          )
         )
         (block (result (ref $2))
          (local.set $2
           (struct.new $4
            (ref.func $func0)
            (struct.new $1
             (local.get $0)
             (local.get $1)
            )
           )
          )
          (block (result (ref $2))
           (call $print_i32
            (struct.get $0 0
             (ref.cast (ref $0)
              (call_ref $3
               (struct.new $0
                (i32.const 3)
               )
               (struct.get $4 1
                (ref.cast (ref $4)
                 (local.get $2)
                )
               )
               (struct.get $4 0
                (ref.cast (ref $4)
                 (local.get $2)
                )
               )
              )
             )
            )
           )
           (struct.new_default $2)
          )
         )
        )
       )
      )
     )
    )
    |}]
