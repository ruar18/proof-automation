# proof-automation
Automate the generation of certain homomorphism proofs in Dafny. 

## Using the Script
Run `generate_proof` in `src/program_loader.py`, passing in the names of the input
and output files. Input format should follow that given in the examples.

## Known Issues
* Running the output using the Dafny VSCode extension can sometimes result in the error `assertion violation (timed out)` when Dafny attempts to verify the line `assert (s + t1) + t2 == s + t;` in the homomorphism proofs. Running Dafny through the command line appears to solve this issue.
