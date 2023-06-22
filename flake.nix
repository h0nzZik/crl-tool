{
  description = "An implementation of Cartesian Reachability Logic via K";
  inputs = {
    # We cannot work with nixpkgs-unstable because of this change: https://github.com/NixOS/nixpkgs/pull/238764.
    # That change needs to be reflected in Mavenix. Until then, we stay at `nixos-23.05`.
    #nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.05";
    
    pyk.url = "github:runtimeverification/pyk/v0.1.337";
    pyk.inputs.nixpkgs.follows = "nixpkgs";
    
    #k-framework.url = "github:runtimeverification/k";
    k-framework.url = "github:h0nzZik/k/cartesian-rl";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";

    k-haskell-backend.follows = "k-framework/haskell-backend";
  };

  outputs = { self, nixpkgs, pyk, k-framework, k-haskell-backend, ... }:
    let
      forAllSystems = f: nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed (system: f system);
      pkgs = forAllSystems (system:  nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python311;
        stdenv = pkgs.${system}.stdenv;
        k = k-framework.packages.${system}.k;
        python-pyk = pyk.packages.${system}.pyk-python311 ;

        crl-tool = python.pkgs.buildPythonApplication {
            name = "crl-tool";
            src = ./crltool;
            format = "pyproject";
            propagatedBuildInputs = [
              python-pyk
              python.pkgs.setuptools
            ];
            postInstall = ''
              substituteInPlace $out/lib/*/site-packages/crltool/kcommands.py \
                --replace "\"kompile\"" "\"${k}/bin/kompile\""
              substituteInPlace $out/lib/*/site-packages/crltool/kcommands.py \
                --replace "\"kprove\"" "\"${k}/bin/kprove\""
              substituteInPlace $out/lib/*/site-packages/crltool/kcommands.py \
                --replace "\"kore-rpc\"" "\"${k}/bin/kore-rpc\""
            '';
        };

        test = stdenv.mkDerivation {
          name = "crl-tool-test" ;
          src = ./test ;
          propagatedBuildInputs = [
            crl-tool
            k
            python-pyk
          ] ;

          buildPhase = "make default";
          installPhase = "echo 'Empty install phase'";
        };

        default = crl-tool ;

      in {
        inherit crl-tool;
        inherit test;
        inherit default;
      });
    };
}
