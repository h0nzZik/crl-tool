{
  description = "An implementation of Cartesian Reachability Logic via K";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    pyk.url = "github:runtimeverification/pyk/v0.1.94";
    #pyk.url = "/home/jan/projects/rv/pyk";
    #k-framework.url = "github:runtimeverification/k";
    k-framework.url = "github:h0nzZik/k/dont-prove";
    k-haskell-backend.follows = "k-framework/haskell-backend";
  };

  outputs = { self, nixpkgs, pyk, k-framework, k-haskell-backend }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      pkgs = forAllSystems (system: nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python310;
        stdenv = pkgs.${system}.stdenv;
        pythonPackages = pkgs.${system}.python310Packages;
        k = k-framework.packages.${system}.k;
        kore-rpc = k-haskell-backend.projectGhc9.${system}.hsPkgs.kore.components.exes.kore-rpc;
        python-pyk = pyk.packages.${system}.pyk-python310 ;
      in {
        crl-tool = python.pkgs.buildPythonApplication {
            name = "crl-tool";
            src = ./crltool;
            format = "pyproject";
            propagatedBuildInputs = [
              python-pyk
              python.pkgs.setuptools
              python.pkgs.pygtrie
            ];
            postInstall = ''
              substituteInPlace $out/lib/*/site-packages/crltool/kcommands.py \
                --replace "\"kompile\"" "\"${k}/bin/kompile\""
              substituteInPlace $out/lib/*/site-packages/crltool/kcommands.py \
                --replace "\"kprove\"" "\"${k}/bin/kprove\""
              substituteInPlace $out/lib/*/site-packages/crltool/kcommands.py \
                --replace "\"kore-rpc\"" "\"${kore-rpc}/bin/kore-rpc\""
            '';
        };

        test = stdenv.mkDerivation {
          name = "crl-tool-test" ;
          src = ./test ;
          propagatedBuildInputs = [
            self.outputs.packages.${system}.crl-tool
            k
            kore-rpc
            python-pyk
          ] ;

          buildPhase = "make default";
          installPhase = "echo 'Empty install phase'";
        };

        default = self.outputs.packages.${system}.crl-tool ;
      });
    };
}
