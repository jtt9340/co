let nixpkgs = import ./moz_overlay.nix;
in with nixpkgs;
pkgs.buildEnv {
  name = "co_env";

  paths = [
    (latest.rustChannels.stable.rust.override { extensions = [ "rust-src" ]; })
  ];
}
