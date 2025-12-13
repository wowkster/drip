#!/usr/bin/env python3

import os
import subprocess
from sys import stderr

if __name__ == "__main__":
    # Build the latest compiler

    code = os.system("cargo build")
    if code != 0:
        print(f"Failed to build the compiler (exited with code {code})")
        exit(1)

    # Run the compiler on all the test cases

    base_names = []

    # TODO: theres a better way to do this without doing more path checks
    for file in os.listdir("examples"):
        if file.endswith(".output.txt"):
            base_name = file.rstrip(".output.txt")

            if os.path.exists(f"examples/{base_name}.drip"):
                base_names.append(base_name)

    print(f"Running {len(base_names)} tests:", base_names)

    for base_name in sorted(base_names):
        # Read the expected output
        file = open(f"examples/{base_name}.output.txt", "rb")
        expected = file.read()
        file.close()

        # Compile the example
        code = os.system(
            f"target/debug/dripc -O0 -o build/example-{base_name} examples/{base_name}.drip"
        )

        if code != 0:
            print(
                f"Failed to compile example {base_name} (exited with code {code})",
                file=stderr,
            )
            exit(1)
            
        code = os.system(
            f"target/debug/dripc -O0 -o build/example-{base_name}.s examples/{base_name}.drip"
        )

        # Run the example
        output = subprocess.check_output(
            [f"build/example-{base_name}"]
        )

        if output != expected:
            print(f"Test {base_name} failed! Output did not equal expected.")
            print("output:", output)
            print("expected:", expected)
            exit(1)
        else:
            print(f"Test {base_name} passed!")

    exit(0)
