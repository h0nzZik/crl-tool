{ sources ? import ./sources.nix
}:
let
  # default nixpkgs
  pkgs = import sources.nixpkgs { };

  # gitignore.nix 
  gitignoreSource = (import sources."gitignore.nix" { inherit (pkgs) lib; }).gitignoreSource;

  pre-commit-hooks = (import sources."pre-commit-hooks.nix");

  k-haskell-backend-project = (import sources."haskell-backend" {});

  src = gitignoreSource ./..;

  # see https://github.com/tweag/haskell-stack-nix-example/blob/main/shell.nix
  # Wrap Stack to configure Nix integration and target the correct Stack-Nix file
  #
  # - nix: Enable Nix support
  # - no-nix-pure: Pass environment variables, like `NIX_PATH`
  # - nix-shell-file: Specify the Nix file to use (otherwise it uses `shell.nix` by default)
  stack-wrapped = pkgs.symlinkJoin {
    name = "stack";
    paths = [ pkgs.stack ];
    buildInputs = [ pkgs.makeWrapper ];
    postBuild = ''
      wrapProgram $out/bin/stack \
        --add-flags "\
          --nix \
          --no-nix-pure \
          --nix-shell-file=nix/stack-integration.nix \
        "
    '';
  };

  #kore-libs = pkgs.symlinkJoin {
  #  name = "kore-libs";
  #  paths = pkgs.lib.attrValues k-haskell-backend-project.project.kore.components.sublibs;
  #};

  kore-libs = k-haskell-backend-project.project.kore.components.library ;

in
{
  inherit pkgs src;

  #inherit (pkgs) cabal-install ghcid stack;

  # provided by shell.nix
  devTools = {
    inherit (pkgs) niv;
    inherit (pre-commit-hooks) pre-commit;
    inherit (k-haskell-backend-project) kore;
#    inherit (pkgs.haskellPackages) ghc;
    inherit stack-wrapped;
    inherit kore-libs;
  };

  # to be built by github actions
  ci = {
    pre-commit-check = pre-commit-hooks.run {
      inherit src;
      hooks = {
        shellcheck.enable = true;
        nixpkgs-fmt.enable = true;
        nix-linter.enable = true;
      };
      # generated files
      excludes = [ "^nix/sources\.nix$" ];
    };
  };
}
