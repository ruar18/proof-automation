import program_loader


def main():
    paths = ["examples/ml_example", "examples/mtlr_example",
             "examples/mts_example"]
    for path in paths:
        program_loader.generate_proof(f"{path}/example_input.txt",
                                      f"{path}/output.dfy")


if __name__ == "__main__":
    main()
