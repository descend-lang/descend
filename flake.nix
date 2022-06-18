{
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = (import nixpkgs { inherit system; config = { allowUnfree = true; }; });
        in
        let buildInputs = with pkgs; [
          rustc
          cargo
          gcc
          pkgconfig
          libconfig
          cmake
          rustfmt
          clippy
          clang-tools
          gdb
          cudaPackages.cudatoolkit
          linuxPackages.nvidia_x11
        ]; in
        {
          nixpkgs.config.allowUnfree = true;
          devShell = pkgs.mkShell
            {
              buildInputs = buildInputs;
              RUST_SRC_PATH = "${pkgs.rust.packages.stable.rustPlatform.rustLibSrc}";
              shellHook = ''
                export CUDA_PATH=${pkgs.cudatoolkit}
              '';
            };
        });
}
