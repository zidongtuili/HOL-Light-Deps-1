{
  monadlib =
    { stdenv, ocaml, fetchFromGitHub, findlib, ocaml_batteries }:

    stdenv.mkDerivation {

      name = "monadlib";
      version = "0.2";

      src = fetchFromGitHub {
        owner = "Chattered";
        repo = "ocaml-monad";
        rev = "master";
        sha256 = "1d6mh6xpjrw433qcspivc18acsmp5sn4fsvfbbj2h9fpxkviikid";
      };

      buildInputs = [ ocaml ocaml_batteries findlib ];

      createFindlibDestdir = true;

      configurePhase = "ocaml setup.ml -configure --prefix $out";

      buildPhase = "ocaml setup.ml -build";

      installPhase = "ocaml setup.ml -install";

      meta = with stdenv.lib; {
        description = "Monad library";
        license = licenses.mit;
        maintainers = [ stdenv.lib.maintainers.chattered  ];
      };
    };
}
