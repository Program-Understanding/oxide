	.file	"goto_check2.c"
	.text
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movl	$5, -12(%rbp)
.L2:
	movl	$7, -8(%rbp)
	movl	$10, -4(%rbp)
	cmpl	$4, -8(%rbp)
	jle	.L3
	jmp	.L2
.L3:
	movl	-4(%rbp), %eax
	cltq
	movq	%rax, %rdi
	movl	$0, %eax
	call	printf@PLT
	movl	$5, %eax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.3.0-27ubuntu1~18.04) 7.3.0"
	.section	.note.GNU-stack,"",@progbits
