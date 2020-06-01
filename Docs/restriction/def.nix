{ pkgs ? import <nixpkgs> {} }:

let

  texPackages = {
    inherit (pkgs.texlive)
      scheme-basic enumitem mathtools ms pgf tikz-cd ulem xcolor xypic;
  };

in {

  note = pkgs.texFunctions.runLaTeX {
    rootFile = ./note.tex;
    inherit texPackages;
  };

}
