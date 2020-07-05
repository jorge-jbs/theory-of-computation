{ pkgs ? import <nixpkgs> {} }:

with pkgs;

mkShell {
  buildInputs = [
    (agda.withPackages (p: [ p.standard-library p.cubical ]))
  ];
}
