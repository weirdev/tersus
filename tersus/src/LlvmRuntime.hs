module LlvmRuntime
    ( runtimeSource
    ) where

-- The C runtime that the emitted LLVM IR calls: what the program does that is not an instruction. `tersus build` writes
-- it beside the IR and compiles both with clang.
runtimeSource :: String
runtimeSource =
    unlines
        [ "#include <stdint.h>"
        , "#include <stdio.h>"
        , "#include <stdlib.h>"
        , ""
        , "// An Int left its 64 bits: the same message and exit status as `tersus run`"
        , "void tersus_overflow(void) {"
        , "    fputs(\"Evaluation failed: Integer overflow\\n\", stderr);"
        , "    exit(1);"
        , "}"
        , ""
        , "void tersus_print_int(int64_t value) {"
        , "    printf(\"%lld\\n\", (long long)value);"
        , "}"
        , ""
        , "void tersus_print_bool(int value) {"
        , "    puts(value ? \"true\" : \"false\");"
        , "}"
        ]
