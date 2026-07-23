# PickleForth Makefile for macOS on Apple Silicon
# Uses clang (Xcode) to assemble and link

CC = clang
CFLAGS = -arch arm64 -target arm64-apple-darwin
ASFLAGS = -arch arm64 -g
LDFLAGS = -arch arm64 -e _main

TARGET = pickleforth
ASM_SRC = forth.s

.PHONY: all clean test

all: $(TARGET)

$(TARGET): $(ASM_SRC)
	$(CC) $(ASFLAGS) $(LDFLAGS) -o $(TARGET) $(ASM_SRC)
	@echo "Built $(TARGET) successfully!"

clean:
	rm -f $(TARGET)

test: $(TARGET)
	./$(TARGET)
