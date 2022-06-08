{ project ? import ./nix { }
}:

let
  dt = project.devTools ;
in
project.pkgs.mkShell {
  buildInputs = builtins.attrValues project.devTools ;
  #shellHook = ''
  #  ${project.ci.pre-commit-check.shellHook}
  #'';

  # https://github.com/tweag/haskell-stack-nix-example/blob/main/shell.nix
  # Configure the Nix path to our own `pkgs`, to ensure Stack-with-Nix uses the correct one rather than the global <nixpkgs> when looking for the right `ghc` argument to pass in `nix/stack-integration.nix`
  # See https://nixos.org/nixos/nix-pills/nix-search-paths.html for more information
  NIX_PATH = "nixpkgs=" + project.pkgs.path;
}
