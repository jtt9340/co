let
  moz_overlay = import (builtins.fetchTarball
    "https://github.com/mozilla/nixpkgs-mozilla/archive/master.tar.gz");
  nixpkgs = import <nixpkgs> { overlays = [ moz_overlay ]; };
in with nixpkgs;
stdenv.mkDerivation {
  name = "co_shell";

  # Just selecting "rust" from latest.rustChannels.stable installs
  # the whole kit and caboodle: rustc, cargo, rustfmt, rust-gdb, etc...
  buildInputs = [ latest.rustChannels.stable.rust ];
}
