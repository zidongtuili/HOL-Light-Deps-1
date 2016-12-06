{ stdenv, fetchFromGitHub, ocamlPackages }:
  stdenv.mkDerivation {
    name     = "hol_light-2015-11-02";

    src = fetchFromGitHub {
      owner  = "jrh13";
      repo   = "hol-light";
      rev    = "6573d7767dd769890ff21f17050a4fd6c92d207c";
      sha256 = "0q8flbsn4hnimxlv4ci87yx4kjlkk5m1z1ilbgzmlbwgghjmidnh";
    };

    buildInputs = with ocamlPackages; [ findlib ocaml camlp5_strict ];

    patches = [ ./Makefile.patch ];

    installPhase = ''
      cp -a . $out
    '';
}
