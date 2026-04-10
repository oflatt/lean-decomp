.PHONY: build test clean

# Build the main library
build:
	lake build

# Run tests by building the test library
# Tests use #guard_msgs which fail at compile time if assertions don't match
test:
	lake build LeanDecompTest

# Clean build artifacts
clean:
	lake clean
