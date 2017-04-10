(*needs "lib.ml";;*)

(* Rose trees *)
type 'a rose_tree = Rose of 'a * 'a rose_tree list;;

let (rose : 'a -> 'a rose_tree) = fun x -> Rose (x,[]);;

(* Rose trees with holes. *)
type 'a rose_bud =
  Rose_bud of ('a rose_tree list -> 'a rose_tree * 'a rose_tree list);;

(* Apply a rose bud. *)
let (bloom : 'a rose_bud -> 'a rose_tree list -> 'a rose_tree * 'a rose_tree list) =
  fun bud roses -> let Rose_bud f = bud in f roses;;

let rec (map_accum_r : ('a -> 'b -> 'c * 'b) -> 'b -> 'a list -> 'c list * 'b) =
  fun f b -> function
             | []    -> [],b
             | x::xs -> let y,c  = f x b in
                        let ys,d = map_accum_r f c xs in
                        y::ys,d;;

let (seqbuds : 'a rose_bud -> 'a rose_bud list -> 'a rose_bud) = fun bud buds ->
  Rose_bud (fun rs -> bloom bud (let r,rs = map_accum_r bloom rs buds in r@rs));;

let (rotate_p : 'a list -> 'a list) = fun xs -> tl xs @ [hd xs];;
let (rotate_n : 'a list -> 'a list) = fun xs -> last xs :: butlast xs;;

let (rotate_bud_p : 'a rose_bud -> 'a rose_bud) =
  fun bud -> Rose_bud (fun rs -> bloom bud (rotate_p rs));;
let (rotate_bud_n : 'a rose_bud -> 'a rose_bud) =
  fun bud -> Rose_bud (fun rs -> bloom bud (rotate_n rs));;

let (bloom_all : 'a rose_bud list list -> 'a rose_tree list) = fun xs ->
  let rec go acc = function
    | []      -> acc
    | xs::xss ->
       let ys,[] = map_accum_r bloom acc xs in
       go ys xss in
  go [] xs;;

(* Rose bud with root x and n child holes. *)
let (rose_split : int -> 'a -> 'a rose_bud) =
  fun n x -> Rose_bud (fun roses ->
                       let roses,roses' = chop_list n roses in
                       Rose (x,roses), roses');;

let rec (print_rose_tree :
           (Format.formatter -> 'a -> unit) ->
           Format.formatter -> 'a rose_tree -> unit) =
  fun p fmt (Rose (x,xs)) ->
        match xs with
        | [] -> Batformat.fprintf fmt "@[%a@]" p x
        | xs ->
           Batformat.fprintf
             fmt
             "(|@[<hv 2>@[<v>%a@],@,@[<v>%a@]@]|)"
             p
             x
             (Batformat.pp_print_list ~pp_sep:(fun fmt () -> Batformat.fprintf fmt "@,")
                                      (print_rose_tree p))
             xs
