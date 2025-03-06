LEC_DIR := ../EE546_EC_GN_FP
BUILD_DIR := ./build

SOURCES := SL2.md


SOURCES     := $(wildcard $(SOURCES)/*.md) 

all: $(SOURCES)
	python ./dm.py $(LEC_DIR)/$@ > $(BUILD_DIR)/$@
