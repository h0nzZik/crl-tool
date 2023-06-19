{
  description = "An implementation of Cartesian Reachability Logic via K";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    poetry2nix.url = "github:nix-community/poetry2nix/master";

    pyk.url = "github:runtimeverification/pyk/v0.1.337";
    pyk.inputs.nixpkgs.follows = "nixpkgs";
    pyk.inputs.poetry2nix.follows = "poetry2nix";
    #k-framework.url = "github:runtimeverification/k";
    k-framework.url = "github:h0nzZik/k/crl-dontprove";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";

    k-haskell-backend.follows = "k-framework/haskell-backend";
  };

  outputs = { self, nixpkgs, pyk, k-framework, k-haskell-backend, poetry2nix }:
    let
      forAllSystems = f: nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed (system: f system);
      #pkgs = forAllSystems (system:  nixpkgs.legacyPackages.${system});
      pkgs = forAllSystems (system: 
        import nixpkgs {
          inherit system;
          overlays = [ k-framework.overlay k-haskell-backend.overlay ];
        }  
      );
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python311;
        stdenv = pkgs.${system}.stdenv;
        #pythonPackages = pkgs.${system}.python311Packages;
        k = k-framework.packages.${system}.k;
        #k = pkgs.${system}.k-framework;
        #kore-rpc = k-haskell-backend.projectGhc9.${system}.hsPkgs.kore.components.exes.kore-rpc;
        python-pyk = pyk.packages.${system}.pyk-python311 ;

        crl-tool = python.pkgs.buildPythonApplication {
            name = "crl-tool";
            src = ./crltool;
            format = "pyproject";
            propagatedBuildInputs = [
              python-pyk
              python.pkgs.setuptools
              #python.pkgs.pygtrie
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
            #kore-rpc
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
