#!/bin/bash

# Build script for compiling Typst files
# Can be used standalone or as a git pre-commit hook

# --- Configuration ---
SOURCE_DIR="./src"
OUTPUT_DIR="./out"
EXCLUDE_DIR="./cyan-report"
# ---------------------

# Check if running as pre-commit hook
IS_PRECOMMIT=false
if [ "$1" = "--pre-commit" ]; then
    IS_PRECOMMIT=true
    echo "--- Running Typst compilation (pre-commit mode) ---"
else
    echo "--- Building Typst documents ---"
fi

# 1. Check if the source directory exists
if [ ! -d "$SOURCE_DIR" ]; then
    echo "!!! ERROR: Source directory '$SOURCE_DIR' not found."
    exit 1
fi

# 2. Create the output directory
mkdir -p "$OUTPUT_DIR"

# 3. Change into the source directory to resolve relative paths
cd "$SOURCE_DIR" || { echo "Failed to change directory to $SOURCE_DIR"; exit 1; }

# 4. Find all .typ files and compile them
COMPILATION_FAILED=false
find . -name "*.typ" -type f -not -path "$EXCLUDE_DIR/*" -print0 | while IFS= read -r -d $'\0' source_file_relative; do

    # Extract the base filename (e.g., 'document.typ' from './document.typ')
    base_name=$(basename "$source_file_relative" .typ)

    # Define the output PDF path
    output_pdf="../out/$base_name.pdf"

    echo "Compiling $source_file_relative -> $output_pdf..."

    # Run the Typst compiler
    typst compile "$source_file_relative" "$output_pdf"

    # Check the exit status
    if [ $? -eq 0 ]; then
        echo "  ✓ Compilation successful"

        # If pre-commit mode, stage the PDF
        if [ "$IS_PRECOMMIT" = true ]; then
            cd ..
            git add "$OUTPUT_DIR/$base_name.pdf"
            cd "$SOURCE_DIR"
        fi
    else
        echo "  ✗ ERROR: Compilation failed for $source_file_relative"
        COMPILATION_FAILED=true
        cd ..
        exit 1
    fi
done

# Change back to the repository root
cd ..

if [ "$COMPILATION_FAILED" = true ]; then
    echo "--- Build failed ---"
    exit 1
fi

echo "--- Build complete ---"
exit 0
