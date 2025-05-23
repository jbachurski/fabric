open Core
open Alg

module type EntryS = sig
  type 'a t [@@deriving sexp, equal, compare]

  val implicit_in_rest : _ t -> bool
  val components : 'a t -> 'a list
  val polar_map : ('a -> 'b) Polar.t -> 'a t -> 'b t
  val map : f:('a -> 'b) -> 'a t -> 'b t
  val pretty : ('a -> Sexp.t) -> 'a t -> Sexp.t
  val meet : 'a lattice -> 'a t -> 'a t -> 'a t
  val join : 'a lattice -> 'a t -> 'a t -> 'a t
end

module Row (Key : String_id.S) (Entry : EntryS) : sig
  type 'a t = { m : 'a Entry.t Key.Map.t; rest : 'a Entry.t }
  [@@deriving sexp, equal, compare]

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val t_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
  val sexp_of_t : ('a -> Sexp.t) -> 'a t -> Sexp.t
  val pretty : ('a -> Sexp.t) -> 'a t -> Sexp.t list
  val components : 'a t -> 'a list
  val polar_map : f:('a -> 'b) Polar.t -> 'a t -> 'b t
  val map : f:('a -> 'b) -> 'a t -> 'b t
  val lift : ('a Entry.t -> 'b Entry.t -> 'c Entry.t) -> 'a t -> 'b t -> 'c t
  val update : 'a t -> Key.t -> 'a Entry.t -> 'a t
  val field : 'a t -> Key.t -> 'a Entry.t
  val subs : 'a t -> 'b t -> ('a Entry.t * 'b Entry.t) Key.Map.t
end = struct
  type 'a t = { m : 'a Entry.t Key.Map.t; rest : 'a Entry.t }
  [@@deriving sexp, equal, compare]

  let pretty a { m; rest } =
    let open Sexp in
    (Core.Map.to_alist m
    |> List.map ~f:(fun (l, f) ->
           List [ Atom (Key.to_string l); Entry.pretty a f ]))
    @
    match Entry.implicit_in_rest rest with
    | true -> []
    | false -> [ Atom "|"; Entry.pretty a rest ]

  let polar_map ~f { m; rest } =
    { m = Map.map ~f:(Entry.polar_map f) m; rest = Entry.polar_map f rest }

  let map ~f t = polar_map ~f:{ pos = f; neg = f } t
  let update { m; rest } key data = { m = Map.set m ~key ~data; rest }

  let components { m; rest } =
    (Map.data m |> List.concat_map ~f:Entry.components) @ Entry.components rest

  let field { m; rest } key = Map.find m key |> Option.value ~default:rest

  let subs' { m; rest } { m = m'; rest = rest' } =
    Map.merge m m' ~f:(fun ~key:_ -> function
      | `Both (t, t') -> Some (t, t')
      | `Left t -> Some (t, rest')
      | `Right t' -> Some (rest, t'))

  let subs fs fs' =
    subs' fs fs'
    |> Map.add_exn ~key:(Key.of_string "*") ~data:(fs.rest, fs'.rest)

  let lift f first second =
    {
      m = subs' first second |> Map.map ~f:(fun (fd, fd') -> f fd fd');
      rest = f first.rest second.rest;
    }
end
