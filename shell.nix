let nixpkgs = import ./moz_overlay.nix;
in with nixpkgs;
stdenv.mkDerivation {
  name = "co_shell";

  # Just selecting "rust" from latest.rustChannels.stable installs
  # the whole kit and caboodle: rustc, cargo, rustfmt, rust-gdb, etc...
  buildInputs = [ latest.rustChannels.stable.rust ];
}
