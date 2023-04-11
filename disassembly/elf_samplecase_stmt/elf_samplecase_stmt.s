	.file	"sample1_sanitycheck.c"
	.text
	.globl	add
	.type	add, @function
add:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movl	%edi, -4(%rbp)
	movl	%esi, -8(%rbp)
	movl	-4(%rbp), %edx
	movl	-8(%rbp), %eax
	addl	%edx, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	add, .-add
	.globl	main
	.type	main, @function
main:
.LFB1:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movl	$3, %esi
	movl	$1, %edi
	call	add
	movl	%eax, -4(%rbp)
	cmpl	$7, -4(%rbp)
	ja	.L4
	movl	-4(%rbp), %eax
	leaq	0(,%rax,4), %rdx
	leaq	.L6(%rip), %rax
	movl	(%rdx,%rax), %eax
	movslq	%eax, %rdx
	leaq	.L6(%rip), %rax
	addq	%rdx, %rax
	jmp	*%rax
	.section	.rodata
	.align 4
	.align 4
.L6:
	.long	.L4-.L6
	.long	.L5-.L6
	.long	.L7-.L6
	.long	.L8-.L6
	.long	.L9-.L6
	.long	.L10-.L6
	.long	.L11-.L6
	.long	.L12-.L6
	.text
.L5:
	addl	$1, -4(%rbp)
	jmp	.L4
.L7:
	addl	$2, -4(%rbp)
	jmp	.L4
.L8:
	addl	$3, -4(%rbp)
	jmp	.L4
.L9:
	addl	$4, -4(%rbp)
	jmp	.L4
.L10:
	addl	$5, -4(%rbp)
	jmp	.L4
.L11:
	addl	$6, -4(%rbp)
	jmp	.L4
.L12:
	addl	$7, -4(%rbp)
	nop
.L4:
	movl	-4(%rbp), %eax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1:
	.size	main, .-main
	.ident	"GCC: (Ubuntu 7.3.0-27ubuntu1~18.04) 7.3.0"
	.section	.note.GNU-stack,"",@progbits
