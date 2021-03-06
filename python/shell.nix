with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "chc";

  buildInputs = [
    z3
    python3
  ] ++ (with python36Packages; [
    sexpdata
    scikitlearn
    graphviz
    matplotlib
    numpy
    ipdb # debugger
  ]);
}
