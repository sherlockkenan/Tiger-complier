.section .rodata
L44:
.string "    "
L43:
.string "   \n"
L36:
.string "   0"
L35:
.string "   -"
L32:
.string "   0"
L17:
.string "   0"
L9:
.string "   \n"
L8:
.string "    "
L2:
.string "   9"
L1:
.string "   0"
.text
.globl tigermain
.type tigermain, @function
 tigermain:
L49:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl %ebp, %eax
addl $-16, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
movl %ebp, %eax
addl $-20, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
pushl %ebp
call readlist
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
movl %ebp, %eax
addl $-24, %eax
movl %eax, %esi
movl %ebp, %eax
addl $-16, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
pushl %ecx
pushl %edx
pushl %ebp
call readlist
addl $4, %esp
popl %edx
popl %ecx
movl %eax, (%esi)
movl %ebp, %ebx
pushl %ecx
pushl %edx
movl -24(%ebp), %eax
pushl %eax
movl -20(%ebp), %eax
pushl %eax
pushl %ebp
call merge
addl $12, %esp
popl %edx
popl %ecx
movl %eax, %eax
pushl %ecx
pushl %edx
pushl %eax
pushl %ebx
call printlist
addl $8, %esp
popl %edx
popl %ecx
jmp L48
L48:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl printlist
.type printlist, @function
 printlist:
printlist:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl 12(%ebp), %eax
movl $0x0, %ebx
cmp %ebx, %eax
je L45
L46:
pushl %ecx
pushl %edx
movl 12(%ebp), %eax
movl 0(%eax), %eax
pushl %eax
movl 8(%ebp), %eax
pushl %eax
call printint
addl $8, %esp
popl %edx
popl %ecx
pushl %ecx
pushl %edx
pushl $L44
call print
addl $4, %esp
popl %edx
popl %ecx
pushl %ecx
pushl %edx
movl 12(%ebp), %eax
movl 4(%eax), %eax
pushl %eax
movl 8(%ebp), %eax
pushl %eax
call printlist
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
L47:
jmp L50
L45:
pushl %ecx
pushl %edx
pushl $L43
call print
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
jmp L47
L50:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl printint
.type printint, @function
 printint:
printint:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl 12(%ebp), %eax
movl $0x0, %ebx
cmp %ebx, %eax
jl L40
L41:
movl 12(%ebp), %eax
movl $0x0, %ebx
cmp %ebx, %eax
jg L37
L38:
pushl %ecx
pushl %edx
pushl $L36
call print
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
L39:
movl %eax, %eax
L42:
jmp L51
L40:
pushl %ecx
pushl %edx
pushl $L35
call print
addl $4, %esp
popl %edx
popl %ecx
pushl %ecx
pushl %edx
movl $0,%ebx
movl 12(%ebp), %eax
subl %eax, %ebx
pushl %ebx
pushl %ebp
call f
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
jmp L42
L37:
pushl %ecx
pushl %edx
movl 12(%ebp), %eax
pushl %eax
pushl %ebp
call f
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
jmp L39
L51:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl f
.type f, @function
 f:
f:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl 12(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
jg L33
L34:
jmp L52
L33:
pushl %ecx
pushl %edx
movl 12(%ebp), %ecx
movl $0xa, %ebx
pushl %edx
pushl %eax
movl %ecx, %eax
movl $0, %edx
pushl %ebx
idivl (%esp)
movl %eax, %ecx
popl %ebx
popl %eax
popl %edx
pushl %ecx
movl 8(%ebp), %eax
pushl %eax
call f
addl $8, %esp
popl %edx
popl %ecx
movl 12(%ebp), %edi
movl 12(%ebp), %esi
movl $0xa, %ebx
pushl %edx
pushl %eax
movl %esi, %eax
movl $0, %edx
pushl %ebx
idivl (%esp)
movl %eax, %esi
popl %ebx
popl %eax
popl %edx
movl %esi, %eax
imull $10, %eax
subl %eax, %edi
movl %edi, %ebx
pushl %ecx
pushl %edx
pushl $L32
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
pushl %ecx
pushl %edx
addl %eax, %ebx
pushl %ebx
call chr
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
pushl %ecx
pushl %edx
pushl %eax
call print
addl $4, %esp
popl %edx
popl %ecx
jmp L34
L52:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl merge
.type merge, @function
 merge:
merge:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl 12(%ebp), %eax
movl $0x0, %ebx
cmp %ebx, %eax
je L29
L30:
movl 16(%ebp), %eax
movl $0x0, %ebx
cmp %ebx, %eax
je L26
L27:
movl 12(%ebp), %eax
movl 0(%eax), %ebx
movl 16(%ebp), %eax
movl 0(%eax), %eax
cmp %eax, %ebx
jl L23
L24:
pushl %ecx
pushl %edx
movl $0x8, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
movl 16(%ebp), %eax
movl 0(%eax), %eax
movl %eax, 0(%ebx)
movl %ebx, %eax
addl $4, %eax
movl %eax, %esi
pushl %ecx
pushl %edx
movl 16(%ebp), %eax
movl 4(%eax), %eax
pushl %eax
movl 12(%ebp), %eax
pushl %eax
movl 8(%ebp), %eax
pushl %eax
call merge
addl $12, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%esi)
movl %ebx, %eax
L25:
movl %eax, %eax
L28:
movl %eax, %eax
L31:
movl %eax, %eax
jmp L53
L29:
movl 16(%ebp), %eax
movl %eax, %eax
jmp L31
L26:
movl 12(%ebp), %eax
movl %eax, %eax
jmp L28
L23:
pushl %ecx
pushl %edx
movl $0x8, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
movl 12(%ebp), %eax
movl 0(%eax), %eax
movl %eax, 0(%ebx)
movl %ebx, %eax
addl $4, %eax
movl %eax, %esi
pushl %ecx
pushl %edx
movl 16(%ebp), %eax
pushl %eax
movl 12(%ebp), %eax
movl 4(%eax), %eax
pushl %eax
movl 8(%ebp), %eax
pushl %eax
call merge
addl $12, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%esi)
movl %ebx, %eax
jmp L25
L53:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl readlist
.type readlist, @function
 readlist:
readlist:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl %ebp, %eax
addl $-16, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
movl $0x4, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl $0x0, %esi
movl %esi, 0(%eax)
movl %eax, (%ebx)
movl %ebp, %eax
addl $-20, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
movl -16(%ebp), %eax
pushl %eax
movl 8(%ebp), %eax
pushl %eax
call readint
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
movl -16(%ebp), %eax
movl 0(%eax), %eax
movl $0x0, %ebx
cmp %ebx, %eax
je L21
L20:
pushl %ecx
pushl %edx
movl $0x8, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
movl -20(%ebp), %eax
movl %eax, 0(%ebx)
movl %ebx, %eax
addl $4, %eax
movl %eax, %esi
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
pushl %eax
call readlist
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%esi)
movl %ebx, %eax
L22:
movl %eax, %eax
jmp L54
L21:
movl $0x0, %eax
movl %eax, %eax
jmp L22
L54:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl readint
.type readint, @function
 readint:
readint:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
movl $0x0, %eax
movl %eax, -16(%ebp)
pushl %ecx
pushl %edx
pushl %ebp
call skipto
addl $4, %esp
popl %edx
popl %ecx
movl 12(%ebp), %eax
movl %eax, %eax
addl $0, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
movl -16(%eax), %eax
pushl %eax
pushl %ebp
call isdigit
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
L18:
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
movl -16(%eax), %eax
pushl %eax
pushl %ebp
call isdigit
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl $0x0, %ebx
cmp %ebx, %eax
je L16
L19:
movl %ebp, %eax
addl $-16, %eax
movl %eax, %esi
movl -16(%ebp), %eax
movl %eax, %eax
imull $10, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
movl -16(%eax), %eax
pushl %eax
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
addl %eax, %ebx
movl %ebx, %ebx
pushl %ecx
pushl %edx
pushl $L17
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
subl %eax, %ebx
movl %ebx, (%esi)
movl 8(%ebp), %eax
movl %eax, %eax
addl $-16, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
jmp L18
L16:
movl -16(%ebp), %eax
movl %eax, %eax
jmp L55
L55:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl skipto
.type skipto, @function
 skipto:
skipto:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
L14:
pushl %ecx
pushl %edx
pushl $L8
movl 8(%ebp), %eax
movl 8(%eax), %eax
movl -16(%eax), %eax
pushl %eax
call stringEqual
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl $0x0, %ebx
cmp %ebx, %eax
je L11
L10:
movl $0x1, %eax
movl %eax, %ebx
L12:
movl $0x0, %eax
cmp %eax, %ebx
je L13
L15:
movl 8(%ebp), %eax
movl 8(%eax), %eax
movl %eax, %eax
addl $-16, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, (%ebx)
jmp L14
L11:
pushl %ecx
pushl %edx
pushl $L9
movl 8(%ebp), %eax
movl 8(%eax), %eax
movl -16(%eax), %eax
pushl %eax
call stringEqual
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %ebx
jmp L12
L13:
jmp L56
L56:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



.text
.globl isdigit
.type isdigit, @function
 isdigit:
isdigit:
pushl %ebp
movl %esp,%ebp
pushl %ebx
pushl %edi
pushl %esi
subl $200,%esp
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
movl 8(%eax), %eax
movl -16(%eax), %eax
pushl %eax
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
pushl $L1
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
cmp %eax, %ebx
jge L3
L4:
movl $0x0, %eax
movl %eax, %eax
L5:
movl %eax, %eax
jmp L57
L3:
movl $0x1, %eax
movl %eax, %esi
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
movl 8(%eax), %eax
movl -16(%eax), %eax
pushl %eax
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
movl %eax, %ebx
pushl %ecx
pushl %edx
pushl $L2
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %eax
cmp %eax, %ebx
jle L6
L7:
movl $0x0, %eax
movl %eax, %esi
L6:
movl %esi, %eax
jmp L5
L57:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



