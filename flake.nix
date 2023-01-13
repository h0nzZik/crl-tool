{
  description = "An implementation of Cartesian Reachability Logic via K";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    pyk.url = "github:runtimeverification/pyk/v0.1.94";
  };

  outputs = { self, nixpkgs, pyk }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      pkgs = forAllSystems (system: nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (system:
      let
        python = pkgs.${system}.python310;
        pythonPackages = pkgs.${system}.python310Packages;
      in {
        crl-tool = python.pkgs.buildPythonApplication {
            name = "crltool";
            src = ./crltool;
            format = "pyproject";
            propagatedBuildInputs = [
              pyk.packages.${system}.pyk-python310
              python.pkgs.setuptools
            ];
        };
        default = self.outputs.packages.${system}.crl-tool ;
      });

      devShells = forAllSystems (system: {
        #default = pkgs.${system}.mkShellNoCC {
        #  packages = with pkgs.${system}; [
        #    (poetry2nix.mkPoetryEnv { projectDir = self; })
        #    poetry
        #  ];
        #};
      });
    };
}
