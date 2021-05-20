{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = [ (pkgs.haskellPackages.ghcWithPackages (p: [
    p.extra
  ])) ];
}
