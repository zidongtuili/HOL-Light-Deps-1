{ stdenv, fetchFromGitHub, ocamlPackages }:
  stdenv.mkDerivation {
    name     = "hol_light-2015-11-02";

    src = fetchFromGitHub {
      owner  = "jrh13";
      repo   = "hol-light";
      rev    = "10265313397476ddff4ce13e7bbb588025e7272c";
      sha256 = "17b6a7vk9fhppl0h366y7pw6a9sknq1a8gxqg67dzqpb47vda1n0";
    };

    buildInputs = with ocamlPackages; [ findlib ocaml camlp5_strict ];

    patches = [ ./Makefile.patch ];

    installPhase = ''
      cp -a . $out
    '';
}
