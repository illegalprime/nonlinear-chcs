with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "latex";

  buildInputs = [
    texlive.combined.scheme-full
  ];
}
