open BatPervasives
(* Give batteries modules some names that don't clash with the parsing
   extension.*)
module Batarray = BatArray
module Batconcurrent = BatConcurrent
module Batlist = struct include Monad.MakePlus(Monad.List) include BatList end
module Batmutex = BatMutex
module Batenum = struct
  module App =
    struct
      type 'a m = 'a BatEnum.t
      let return x    = BatEnum.repeat x
      let (<*>) fs xs = BatEnum.map (fun (f,x) -> f x)
                                    (BatEnum.combine (fs,xs))
    end
  include Applicative.Make(App)
  let lift4 f x y z w = f <$> x <*> y <*> z <*> w
  let to_list xs = BatEnum.fold (fun xs x -> x :: xs) [] xs
  include BatEnum
end
module Batset     = struct
  include BatSet
  module Make_ext(Ord : BatInterfaces.OrderedType) = struct
    include BatSet.Make(Ord)
    let of_list xs = Batlist.fold_left (flip add) empty xs
  end
end
module Batmap     = struct
  include BatMap
  let invert m =
    enum m
    |> Batenum.fold (fun m (x,y) ->
                     modify_def (Batset.singleton x) y
                                (Batset.add x) m)
                    empty
    |> map Batset.to_list
  (* Add a binding, returning true if a new binding was added as opposed to
     being merely replaced. *)
  let add' k v m =
    let added = ref false in
    let m = modify_opt k (function
                           | None -> added := true; Some v
                           | v    -> v) m in
    m,!added
  module Make_ext(Ord : BatInterfaces.OrderedType) = struct
    include BatMap.Make(Ord)
    module Keyset = Batset.Make(Ord)
    let invert m =
      enum m
      |> Batenum.fold (fun m (x,y) ->
                       BatMap.modify_def (Keyset.singleton x) y
                                         (Keyset.add x) m)
                      BatMap.empty
      |> BatMap.map Keyset.to_list
    let key_list m = keys m |> Batenum.to_list |> Batlist.rev
    let to_list m = enum m |> Batenum.to_list |> Batlist.rev
  end
end

module Batoption  = struct include Monad.MakePlus(Monad.Option)
                           include BatOption end
module Batprintf  = BatPrintf
module Batscanf   = BatScanf
module Batio      = BatIO
module Batunix    = BatUnix
module Batmarshal = BatMarshal
module Batstring  = BatString
module type Orderedtype = BatInterfaces.OrderedType
