# My Assembler
## Assembler description
- The purpose of assemblers (assembler0, assembler1, ...) is to interact
with our virtual CPU (and RAM). They provide an easy way for byte generation

- Each successive version of the assembler (assembler0, assembler1, ...) is a 
superset of the previous one.

- Every new assembler version compiles down to the language of its predecessor. 
For example, assembler1 translates to assembler0. The only exception is assembler0,
which translates directly to byte-code our CPU can execute.

## Ideas
Consider the following code in assembler1

```
println "Hello, world";
```

This code may be converted to assembler0 in following way:

```
alloc
	12
	72		 // ASCII "H"
	101      // ASCII "e"
	108      // ASCII "l"
	108      // ASCII "l"
	111      // ASCII "o"
	44       // ASCII ","
	32       // ASCII " "
	119      // ASCII "w"
	111      // ASCII "o"
	114      // ASCII "r"
	108      // ASCII "l"
	100;     // ASCII "d"

set r7 accu;    // write the start address of the value
set r6 12;      // write the amount of bytes
set r4 1;       // write the "write" instruction
set r5 1;       // write the "stdout" mode
syscall;        // Invoke syscall
```

Then, this code will be translated into a byte-code.

