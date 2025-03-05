Assembler1:
```
println "Hello, world";
```

Assembler0:

```
alloc
	13       // 13 bytes
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
	100      // ASCII "d"
	10;      // ASCII '\n' 

set r7 accu;    // write the start address of the value
set r6 12;      // write the amount of bytes
set r4 1;       // write the "write" instruction
set r5 1;       // write the "stdout" mode
syscall;        // Invoke syscall
```