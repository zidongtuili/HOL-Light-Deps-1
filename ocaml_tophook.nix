let
  safeX11 = stdenv: !(stdenv.isArm || stdenv.isMips);
in

{ stdenv, fetchgit, fetchFromGitHub, ncurses, buildEnv, libX11, xproto,
  useX11 ? safeX11 stdenv }:

if useX11 && !(safeX11 stdenv)
  then throw "x11 not available in ocaml with arm or mips arch"
  else # let the indentation flow

let
   useNativeCompilers = !stdenv.isMips;
   inherit (stdenv.lib) optionals optionalString;
in

stdenv.mkDerivation rec {

  x11env = buildEnv { name = "x11env"; paths = [libX11 xproto]; };
  x11lib = x11env + "/lib";
  x11inc = x11env + "/include";

  name = "ocaml-4.01.0-tophook";
  version = "4.01.0-tophook";

  src = fetchFromGitHub {
    owner = "Chattered";
    repo = "ocaml";
    # transformer (11.4.17)
    rev = "ae505d6b1d273e66935f1fe705a73266e4318c4d";
    sha256 = "179j7qqcb086x58j2bqjyl8b4vyv26hf23nq7pp288yn0fb7m4r3";
  };

  prefixKey = "-prefix ";
  patches = [ ./fix-clang-build-on-osx.diff ];
  configureFlags = ["-no-tk"] ++ optionals useX11 [ "-x11lib" x11lib
                                                    "-x11include" x11inc ];

  buildFlags =
    "world" + optionalString useNativeCompilers " bootstrap world.opt";
  buildInputs = [ncurses] ++ optionals useX11 [ libX11 xproto ];
  installTargets = "install" + optionalString useNativeCompilers " installopt";
  preConfigure = ''
    CAT=$(type -tp cat)
    sed -e "s@/bin/cat@$CAT@" -i config/auto-aux/sharpbang
  '';
  postBuild = ''
    mkdir -p $out/include
    ln -sv $out/lib/ocaml/caml $out/include/caml
  '';

  passthru = {
    nativeCompilers = useNativeCompilers;
  };

  meta = with stdenv.lib; {
    homepage = http://caml.inria.fr/ocaml;
    branch = "4.01.0-tophook";
    license = with licenses; [
      qpl /* compiler */
      lgpl2 /* library */
    ];
    description = "Most popular variant of the Caml language";

    longDescription =
      ''
        OCaml is the most popular variant of the Caml language.  From a
        language standpoint, it extends the core Caml language with a
        fully-fledged object-oriented layer, as well as a powerful module
        system, all connected by a sound, polymorphic type system featuring
        type inference.

        The OCaml system is an industrial-strength implementation of this
        language, featuring a high-performance native-code compiler (ocamlopt)
        for 9 processor architectures (IA32, PowerPC, AMD64, Alpha, Sparc,
        Mips, IA64, HPPA, StrongArm), as well as a bytecode compiler (ocamlc)
        and an interactive read-eval-print loop (ocaml) for quick development
        and portability.  The OCaml distribution includes a comprehensive
        standard library, a replay debugger (ocamldebug), lexer (ocamllex) and
        parser (ocamlyacc) generators, a pre-processor pretty-printer (camlp4)
        and a documentation generator (ocamldoc).
      '';

    platforms = with platforms; linux ++ darwin;
  };
}
