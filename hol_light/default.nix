{ stdenv, fetchFromGitHub, ocamlPackages }:
  stdenv.mkDerivation {
    name     = "hol_light-2015-11-02";

    src = fetchFromGitHub {
      owner  = "jrh13";
      repo   = "hol-light";
      rev    = "4f87e54ea7b074dfb9e45511a0d003e488f50be2";
      sha256 = "1n6d3fzjc5z35r2nmz1xqlfh2kwqr2v7r5jlwxkw5zd5bznsaw8r";
    };

    buildInputs = with ocamlPackages; [ findlib ocaml camlp5_strict ];

    patches = [ ./Makefile.patch ];

    installPhase = ''
      cp -a . $out
    '';
}
