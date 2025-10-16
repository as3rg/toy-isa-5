li r0, 0
li r1, 1

li r2, 0   # Fib[n - 1]
li r3, 1   # Fib[n    ]

li r4, 8   # n
nor r5, r5, r5

beq r4, r1, 6
add r4, r4, r5

add r6, r2, r0
add r2, r3, r0
add r3, r2, r6

beq r0, r0, -5

li r8, 60
add r0, r0, r3

syscall
