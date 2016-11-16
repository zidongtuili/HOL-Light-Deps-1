let (on : ('a -> 'b) -> ('b -> 'b -> 'c) -> 'a -> 'a -> 'c) =
  fun f p x y -> p (f x) (f y)

let (map_accum_l : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list) =
  fun f b xs ->
  let acc = ref b in
  let ys = List.map (fun x -> let (acc',x') = f !acc x in
                              acc := acc'; x') xs in
  !acc,ys

let rec find_opt p = function
  | [] -> None
  | x::xs when p x -> Some x
  | _::xs -> find_opt p xs

let rec (map_option : ('a -> 'b option) -> 'a list -> 'b list) = fun f xs ->
  match xs with
  | []    -> []
  | x::xs -> match f x with
             | None   -> map_option f xs
             | Some x -> x::map_option f xs

let rec (map_option_acc : ('c -> 'a -> ('c * 'b option))
                          -> 'c -> 'a list -> ('c * 'b list)) =
  fun f acc xs ->
  match xs with
  | []    -> acc,[]
  | x::xs -> let acc',y = f acc x in
             match y with
             | None   -> map_option_acc f acc' xs
             | Some x -> let acc',xs' = map_option_acc f acc' xs in
                         acc',x::xs'

let sum_option_fst x y =
  match x,y with
  | None,None -> None
  | None,Some y -> Some y
  | x,_ -> x
