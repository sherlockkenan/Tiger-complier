.section .rodata
L23:
.string "   \n"
L15:
.string "   \n"
L4:
.string "   y"
L3:
.string "   x"
.text
.globl tigermain
.type tigermain, @function
 tigermain:
L25:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl $0x8, %ebx
movl %ebx, -16(%ebp)
pushl %eax
pushl %ecx
pushl %edx
pushl %ebp
call printb
addl $4, %esp
popl %edx
popl %ecx
jmp L24
L24:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl printb
.type printb, @function
 printb:
printb:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl $0x0, %ebx
movl %ebx, -16(%ebp)
movl 8(%ebp), %ebx
movl -16(%ebx), %ebx
subl $1, %ebx
movl %ebx, -20(%ebp)
movl $0x1, %ebx
movl %ebx, -24(%ebp)
movl $0x0, %esi
movl 8(%ebp), %ebx
movl -16(%ebx), %ebx
subl $1, %ebx
cmp %ebx, %esi
jle L21
L22:
pushl %eax
pushl %ecx
pushl %edx
pushl $L23
call print
addl $4, %esp
popl %edx
popl %ecx
jmp L26
L21:
L19:
movl -24(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
je L1
L20:
movl $0x0, %ebx
movl %ebx, -28(%ebp)
movl 8(%ebp), %ebx
movl -16(%ebx), %ebx
subl $1, %ebx
movl %ebx, -32(%ebp)
movl $0x1, %ebx
movl %ebx, -36(%ebp)
movl $0x0, %esi
movl 8(%ebp), %ebx
movl -16(%ebx), %ebx
subl $1, %ebx
cmp %ebx, %esi
jle L13
L14:
pushl %eax
pushl %ecx
pushl %edx
pushl $L15
call print
addl $4, %esp
popl %edx
popl %ecx
movl -16(%ebp), %ebx
movl -20(%ebp), %esi
cmp %esi, %ebx
jl L16
L17:
movl $0x0, %ebx
movl %ebx, -24(%ebp)
L18:
jmp L19
L13:
L11:
movl -36(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
je L2
L12:
movl -16(%ebp), %ebx
movl -28(%ebp), %esi
cmp %esi, %ebx
jg L5
L6:
movl $L4,%ebx
L7:
pushl %eax
pushl %ecx
pushl %edx
pushl %ebx
call print
addl $4, %esp
popl %edx
popl %ecx
movl -28(%ebp), %ebx
movl -32(%ebp), %esi
cmp %esi, %ebx
jl L8
L9:
movl $0x0, %ebx
movl %ebx, -36(%ebp)
L10:
jmp L11
L5:
movl $L3,%ebx
jmp L7
L8:
movl -28(%ebp), %ebx
addl $1, %ebx
movl %ebx, -28(%ebp)
jmp L10
L2:
jmp L14
L16:
movl -16(%ebp), %ebx
addl $1, %ebx
movl %ebx, -16(%ebp)
jmp L18
L1:
jmp L22
L26:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



