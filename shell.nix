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
}
