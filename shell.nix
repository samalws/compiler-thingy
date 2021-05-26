{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = [
    pkgs.rustc
    (pkgs.haskellPackages.ghcWithPackages (p: [
      p.extra
      p.safe
    ]))
  ];
}
