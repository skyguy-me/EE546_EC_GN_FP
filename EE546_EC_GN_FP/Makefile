PROJECT_DIR := EE546ECGNFP
BUILD_DIR := ./docs

# Find all .lean files in the PROJECT_DIR
SOURCES := $(wildcard $(PROJECT_DIR)/*.lean)

# Define the target files by replacing .lean with .md in the BUILD_DIR
TARGETS := $(patsubst $(PROJECT_DIR)/%.lean, $(BUILD_DIR)/%.md, $(SOURCES))

# Default target to build all .md files
all: $(TARGETS)

# Rule to generate .md files from .lean files
$(BUILD_DIR)/%.md: $(PROJECT_DIR)/%.lean
	@mkdir -p $(BUILD_DIR)
	python ./dm.py $< > $@

# Clean up the build directory
clean:
	rm -rf $(BUILD_DIR)/*.md

.PHONY: all clean
