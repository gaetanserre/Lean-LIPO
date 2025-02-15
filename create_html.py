import os

project = "./LeanLIPO"
print_blue = lambda s: print("\033[94m" + s + "\033[0m")
if not os.path.exists(".lake"):
    print(f".lake not found in {project}. Please run `lake exe cache get` to continue.")
else:
    # Get path to all Lean files
    for file in os.listdir(project):
        if file.endswith(".lean") and not file.startswith("lakefile"):
            lean_file = os.path.join(project, file)
            # Call Alectryon on each Lean file
            os.system(
                f"alectryon --frontend lean4 {lean_file} --lake lakefile.lean --webpage-style windowed --output-directory html"
            )
