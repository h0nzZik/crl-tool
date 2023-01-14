# A Cartesian Reachability Logic tool

## How to build

To enter the environment with the tool in path, run
```sh
nix shell '.#crl-tool'
```

Then, inside the shell, feel free to explore the tool
```sh
crl-tool --help
```

## How to run the tests

Enter the testing environment
```sh
nix develop '.#test'
```
Then, inside the environment, run the tests using
```
make -C test/
```