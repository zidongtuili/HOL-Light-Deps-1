# HOListic
HOL Light Metadata and Dependency Tracker

## Installation Requirements

Install [Nix](https://nixos.org/nix/)

## Quickstart

Clone the repository, and then in the main directory (containing default.nix) run

```
nix-shell
```

This will download, compile and then place you in an environment containing
everything you need to run HOListic. To start HOL Light:

```
cd hollight
ocaml -I $findlib
```

This starts Ocaml with the directory =$findlib= in the Ocaml include path. The file
=.ocamlinit= in the =hollight= directory is automatically loaded, which, in turn,
loads the core of HOL Light. Dependency data is automatically recorded, which you can
convert to JSON with code such as:

```
(* Convert Ocaml metadata to internal JSON. Don't serialise out term trees, nor proofs. *)
let json = all_json ~json_terms:false ~json_proofs:false () in

(* Open "meta.json" for writing. *)
let out = open_out "meta.json" in

(* Output the JSON. *)
let () = output_string out (Ezjsonm.to_string json) in

close_out out;;
```

