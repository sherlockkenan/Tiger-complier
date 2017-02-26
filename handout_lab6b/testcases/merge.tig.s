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
movl %ebp, %ebx
addl $-16, %ebx
movl %ebx, %esi
pushl %eax
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
movl %ebx, (%esi)
pushl %eax
pushl %ecx
pushl %edx
pushl %ebp
call readlist
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %edi
popl %eax
movl %ebp, %ebx
addl $-16, %ebx
movl %ebx, %esi
pushl %eax
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
movl %ebx, (%esi)
pushl %eax
pushl %ecx
pushl %edx
pushl %ebp
call readlist
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
movl %ebp, %esi
pushl %eax
pushl %ecx
pushl %edx
pushl %ebx
pushl %edi
pushl %ebp
call merge
addl $12, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
pushl %eax
pushl %ecx
pushl %edx
pushl %ebx
pushl %esi
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
movl 12(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
je L45
L46:
pushl %eax
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
pushl %eax
pushl %ecx
pushl %edx
pushl $L44
call print
addl $4, %esp
popl %edx
popl %ecx
pushl %eax
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
popl %eax
L47:
jmp L50
L45:
pushl %eax
pushl %ecx
pushl %edx
pushl $L43
call print
addl $4, %esp
popl %edx
popl %ecx
popl %eax
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
movl 12(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
jl L40
L41:
movl 12(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
jg L37
L38:
pushl %eax
pushl %ecx
pushl %edx
pushl $L36
call print
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
L39:
L42:
jmp L51
L40:
pushl %eax
pushl %ecx
pushl %edx
pushl $L35
call print
addl $4, %esp
popl %edx
popl %ecx
pushl %eax
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
movl %eax, %ebx
popl %eax
jmp L42
L37:
pushl %eax
pushl %ecx
pushl %edx
movl 12(%ebp), %eax
pushl %eax
pushl %ebp
call f
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
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
pushl %eax
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
movl %esi, %ebx
imull $10, %ebx
subl %ebx, %edi
movl %edi, %esi
pushl %eax
pushl %ecx
pushl %edx
pushl $L32
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
pushl %eax
pushl %ecx
pushl %edx
addl %ebx, %esi
pushl %esi
call chr
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
pushl %eax
pushl %ecx
pushl %edx
pushl %ebx
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
movl 12(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
je L29
L30:
movl 16(%ebp), %ebx
movl $0x0, %esi
cmp %esi, %ebx
je L26
L27:
movl 12(%ebp), %ebx
movl 0(%ebx), %esi
movl 16(%ebp), %ebx
movl 0(%ebx), %ebx
cmp %ebx, %esi
jl L23
L24:
pushl %eax
pushl %ecx
pushl %edx
movl $0x8, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %esi
popl %eax
movl 16(%ebp), %ebx
movl 0(%ebx), %ebx
movl %ebx, 0(%esi)
movl %esi, %ebx
addl $4, %ebx
movl %ebx, %edi
pushl %eax
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
movl %eax, %ebx
popl %eax
movl %ebx, (%edi)
movl %esi, %eax
L25:
movl %eax, %ebx
L28:
L31:
movl %ebx, %eax
jmp L53
L29:
movl 16(%ebp), %ebx
jmp L31
L26:
movl 12(%ebp), %ebx
jmp L28
L23:
pushl %eax
pushl %ecx
pushl %edx
movl $0x8, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %esi
popl %eax
movl 12(%ebp), %ebx
movl 0(%ebx), %ebx
movl %ebx, 0(%esi)
movl %esi, %ebx
addl $4, %ebx
movl %ebx, %edi
pushl %eax
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
movl %eax, %ebx
popl %eax
movl %ebx, (%edi)
movl %esi, %eax
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
pushl %eax
pushl %ecx
pushl %edx
movl $0x4, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
movl $0x0, %esi
movl %esi, 0(%ebx)
pushl %eax
pushl %ecx
pushl %edx
pushl %ebx
movl 8(%ebp), %eax
pushl %eax
call readint
addl $8, %esp
popl %edx
popl %ecx
movl %eax, %edi
popl %eax
movl 0(%ebx), %ebx
movl $0x0, %esi
cmp %esi, %ebx
je L21
L20:
pushl %eax
pushl %ecx
pushl %edx
movl $0x8, %eax
pushl %eax
call allocRecord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %esi
popl %eax
movl %edi, 0(%esi)
movl %esi, %ebx
addl $4, %ebx
pushl %eax
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
pushl %eax
call readlist
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ecx
popl %eax
movl %ecx, (%ebx)
movl %esi, %eax
L22:
jmp L54
L21:
movl $0x0, %eax
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
movl $0x0, %ebx
movl %ebx, %edi
pushl %eax
pushl %ecx
pushl %edx
pushl %ebp
call skipto
addl $4, %esp
popl %edx
popl %ecx
movl 12(%ebp), %ebx
addl $0, %ebx
movl %ebx, %esi
pushl %eax
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
movl %eax, %ebx
popl %eax
movl %ebx, (%esi)
L18:
pushl %eax
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
movl %eax, %ebx
popl %eax
movl $0x0, %esi
cmp %esi, %ebx
je L16
L19:
movl %edi, %ebx
imull $10, %ebx
movl %ebx, %esi
pushl %eax
pushl %ecx
pushl %edx
movl 8(%ebp), %eax
movl -16(%eax), %eax
pushl %eax
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
addl %ebx, %esi
pushl %eax
pushl %ecx
pushl %edx
pushl $L17
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
subl %ebx, %esi
movl %esi, %edi
movl 8(%ebp), %ebx
addl $-16, %ebx
movl %ebx, %esi
pushl %eax
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
movl %ebx, (%esi)
jmp L18
L16:
movl %edi, %eax
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
pushl %eax
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
movl %eax, %ebx
popl %eax
movl $0x0, %esi
cmp %esi, %ebx
je L11
L10:
movl $0x1, %ebx
movl %ebx, %esi
L12:
movl $0x0, %ebx
cmp %ebx, %esi
je L13
L15:
movl 8(%ebp), %ebx
movl 8(%ebx), %ebx
addl $-16, %ebx
movl %ebx, %esi
pushl %eax
pushl %ecx
pushl %edx
call getchar
addl $0, %esp
popl %edx
popl %ecx
movl %eax, %ebx
popl %eax
movl %ebx, (%esi)
jmp L14
L11:
pushl %eax
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
movl %eax, %esi
popl %eax
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
pushl %eax
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
movl %eax, %ebx
popl %eax
pushl %eax
pushl %ecx
pushl %edx
pushl $L1
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %esi
popl %eax
cmp %esi, %ebx
jge L3
L4:
movl $0x0, %eax
L5:
jmp L57
L3:
movl $0x1, %ebx
movl %ebx, %edi
pushl %eax
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
movl %eax, %ebx
popl %eax
pushl %eax
pushl %ecx
pushl %edx
pushl $L2
call ord
addl $4, %esp
popl %edx
popl %ecx
movl %eax, %esi
popl %eax
cmp %esi, %ebx
jle L6
L7:
movl $0x0, %eax
movl %eax, %edi
L6:
movl %edi, %eax
jmp L5
L57:

movl %ebp,%esp
addl $-12,%esp
popl %esi
popl %edi
popl %ebx
popl %ebp
ret 



