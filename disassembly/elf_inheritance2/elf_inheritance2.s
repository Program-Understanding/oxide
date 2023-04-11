	.file	"inheritance2.cpp"
	.text
	.section	.rodata
	.type	_ZStL19piecewise_construct, @object
	.size	_ZStL19piecewise_construct, 1
_ZStL19piecewise_construct:
	.zero	1
	.local	_ZStL8__ioinit
	.comm	_ZStL8__ioinit,1,1
	.section	.text._ZNK3One6getNumEv,"axG",@progbits,_ZNK3One6getNumEv,comdat
	.align 2
	.weak	_ZNK3One6getNumEv
	.type	_ZNK3One6getNumEv, @function
_ZNK3One6getNumEv:
.LFB1494:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -8(%rbp)
	movl	$1, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1494:
	.size	_ZNK3One6getNumEv, .-_ZNK3One6getNumEv
	.section	.text._ZNK3Two6getNumEv,"axG",@progbits,_ZNK3Two6getNumEv,comdat
	.align 2
	.weak	_ZNK3Two6getNumEv
	.type	_ZNK3Two6getNumEv, @function
_ZNK3Two6getNumEv:
.LFB1495:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -8(%rbp)
	movl	$2, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1495:
	.size	_ZNK3Two6getNumEv, .-_ZNK3Two6getNumEv
	.section	.text._ZNK5Three6getNumEv,"axG",@progbits,_ZNK5Three6getNumEv,comdat
	.align 2
	.weak	_ZNK5Three6getNumEv
	.type	_ZNK5Three6getNumEv, @function
_ZNK5Three6getNumEv:
.LFB1496:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -8(%rbp)
	movl	$3, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1496:
	.size	_ZNK5Three6getNumEv, .-_ZNK5Three6getNumEv
	.section	.text._ZNK4Four6getNumEv,"axG",@progbits,_ZNK4Four6getNumEv,comdat
	.align 2
	.weak	_ZNK4Four6getNumEv
	.type	_ZNK4Four6getNumEv, @function
_ZNK4Four6getNumEv:
.LFB1497:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movq	%rdi, -8(%rbp)
	movl	$1, %eax
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1497:
	.size	_ZNK4Four6getNumEv, .-_ZNK4Four6getNumEv
	.text
	.globl	_Z9getNumberP6Number
	.type	_Z9getNumberP6Number, @function
_Z9getNumberP6Number:
.LFB1498:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movq	%rdi, -8(%rbp)
	movq	-8(%rbp), %rax
	movq	(%rax), %rax
	movq	(%rax), %rax
	movq	-8(%rbp), %rdx
	movq	%rdx, %rdi
	call	*%rax
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1498:
	.size	_Z9getNumberP6Number, .-_Z9getNumberP6Number
	.globl	main
	.type	main, @function
main:
.LFB1499:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$48, %rsp
	movq	%fs:40, %rax
	movq	%rax, -8(%rbp)
	xorl	%eax, %eax
	leaq	16+_ZTV3One(%rip), %rax
	movq	%rax, -40(%rbp)
	leaq	16+_ZTV3Two(%rip), %rax
	movq	%rax, -32(%rbp)
	leaq	16+_ZTV5Three(%rip), %rax
	movq	%rax, -24(%rbp)
	leaq	16+_ZTV4Four(%rip), %rax
	movq	%rax, -16(%rbp)
	leaq	-40(%rbp), %rax
	movq	%rax, %rdi
	call	_Z9getNumberP6Number
	movl	%eax, -44(%rbp)
	leaq	-32(%rbp), %rax
	movq	%rax, %rdi
	call	_Z9getNumberP6Number
	movl	%eax, -44(%rbp)
	leaq	-24(%rbp), %rax
	movq	%rax, %rdi
	call	_Z9getNumberP6Number
	movl	%eax, -44(%rbp)
	leaq	-16(%rbp), %rax
	movq	%rax, %rdi
	call	_Z9getNumberP6Number
	movl	%eax, -44(%rbp)
	movl	-44(%rbp), %eax
	movq	-8(%rbp), %rdx
	xorq	%fs:40, %rdx
	je	.L13
	call	__stack_chk_fail@PLT
.L13:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1499:
	.size	main, .-main
	.weak	_ZTV4Four
	.section	.data.rel.ro.local._ZTV4Four,"awG",@progbits,_ZTV4Four,comdat
	.align 8
	.type	_ZTV4Four, @object
	.size	_ZTV4Four, 24
_ZTV4Four:
	.quad	0
	.quad	_ZTI4Four
	.quad	_ZNK4Four6getNumEv
	.weak	_ZTV5Three
	.section	.data.rel.ro.local._ZTV5Three,"awG",@progbits,_ZTV5Three,comdat
	.align 8
	.type	_ZTV5Three, @object
	.size	_ZTV5Three, 24
_ZTV5Three:
	.quad	0
	.quad	_ZTI5Three
	.quad	_ZNK5Three6getNumEv
	.weak	_ZTV3Two
	.section	.data.rel.ro.local._ZTV3Two,"awG",@progbits,_ZTV3Two,comdat
	.align 8
	.type	_ZTV3Two, @object
	.size	_ZTV3Two, 24
_ZTV3Two:
	.quad	0
	.quad	_ZTI3Two
	.quad	_ZNK3Two6getNumEv
	.weak	_ZTV3One
	.section	.data.rel.ro.local._ZTV3One,"awG",@progbits,_ZTV3One,comdat
	.align 8
	.type	_ZTV3One, @object
	.size	_ZTV3One, 24
_ZTV3One:
	.quad	0
	.quad	_ZTI3One
	.quad	_ZNK3One6getNumEv
	.weak	_ZTI4Four
	.section	.data.rel.ro._ZTI4Four,"awG",@progbits,_ZTI4Four,comdat
	.align 8
	.type	_ZTI4Four, @object
	.size	_ZTI4Four, 24
_ZTI4Four:
	.quad	_ZTVN10__cxxabiv120__si_class_type_infoE+16
	.quad	_ZTS4Four
	.quad	_ZTI6Number
	.weak	_ZTS4Four
	.section	.rodata._ZTS4Four,"aG",@progbits,_ZTS4Four,comdat
	.type	_ZTS4Four, @object
	.size	_ZTS4Four, 6
_ZTS4Four:
	.string	"4Four"
	.weak	_ZTI5Three
	.section	.data.rel.ro._ZTI5Three,"awG",@progbits,_ZTI5Three,comdat
	.align 8
	.type	_ZTI5Three, @object
	.size	_ZTI5Three, 24
_ZTI5Three:
	.quad	_ZTVN10__cxxabiv120__si_class_type_infoE+16
	.quad	_ZTS5Three
	.quad	_ZTI6Number
	.weak	_ZTS5Three
	.section	.rodata._ZTS5Three,"aG",@progbits,_ZTS5Three,comdat
	.type	_ZTS5Three, @object
	.size	_ZTS5Three, 7
_ZTS5Three:
	.string	"5Three"
	.weak	_ZTI3Two
	.section	.data.rel.ro._ZTI3Two,"awG",@progbits,_ZTI3Two,comdat
	.align 8
	.type	_ZTI3Two, @object
	.size	_ZTI3Two, 24
_ZTI3Two:
	.quad	_ZTVN10__cxxabiv120__si_class_type_infoE+16
	.quad	_ZTS3Two
	.quad	_ZTI6Number
	.weak	_ZTS3Two
	.section	.rodata._ZTS3Two,"aG",@progbits,_ZTS3Two,comdat
	.type	_ZTS3Two, @object
	.size	_ZTS3Two, 5
_ZTS3Two:
	.string	"3Two"
	.weak	_ZTI3One
	.section	.data.rel.ro._ZTI3One,"awG",@progbits,_ZTI3One,comdat
	.align 8
	.type	_ZTI3One, @object
	.size	_ZTI3One, 24
_ZTI3One:
	.quad	_ZTVN10__cxxabiv120__si_class_type_infoE+16
	.quad	_ZTS3One
	.quad	_ZTI6Number
	.weak	_ZTS3One
	.section	.rodata._ZTS3One,"aG",@progbits,_ZTS3One,comdat
	.type	_ZTS3One, @object
	.size	_ZTS3One, 5
_ZTS3One:
	.string	"3One"
	.weak	_ZTI6Number
	.section	.data.rel.ro._ZTI6Number,"awG",@progbits,_ZTI6Number,comdat
	.align 8
	.type	_ZTI6Number, @object
	.size	_ZTI6Number, 16
_ZTI6Number:
	.quad	_ZTVN10__cxxabiv117__class_type_infoE+16
	.quad	_ZTS6Number
	.weak	_ZTS6Number
	.section	.rodata._ZTS6Number,"aG",@progbits,_ZTS6Number,comdat
	.align 8
	.type	_ZTS6Number, @object
	.size	_ZTS6Number, 8
_ZTS6Number:
	.string	"6Number"
	.text
	.type	_Z41__static_initialization_and_destruction_0ii, @function
_Z41__static_initialization_and_destruction_0ii:
.LFB1995:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	subq	$16, %rsp
	movl	%edi, -4(%rbp)
	movl	%esi, -8(%rbp)
	cmpl	$1, -4(%rbp)
	jne	.L16
	cmpl	$65535, -8(%rbp)
	jne	.L16
	leaq	_ZStL8__ioinit(%rip), %rdi
	call	_ZNSt8ios_base4InitC1Ev@PLT
	leaq	__dso_handle(%rip), %rdx
	leaq	_ZStL8__ioinit(%rip), %rsi
	movq	_ZNSt8ios_base4InitD1Ev@GOTPCREL(%rip), %rax
	movq	%rax, %rdi
	call	__cxa_atexit@PLT
.L16:
	nop
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1995:
	.size	_Z41__static_initialization_and_destruction_0ii, .-_Z41__static_initialization_and_destruction_0ii
	.type	_GLOBAL__sub_I__Z9getNumberP6Number, @function
_GLOBAL__sub_I__Z9getNumberP6Number:
.LFB1996:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	movl	$65535, %esi
	movl	$1, %edi
	call	_Z41__static_initialization_and_destruction_0ii
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE1996:
	.size	_GLOBAL__sub_I__Z9getNumberP6Number, .-_GLOBAL__sub_I__Z9getNumberP6Number
	.section	.init_array,"aw"
	.align 8
	.quad	_GLOBAL__sub_I__Z9getNumberP6Number
	.hidden	__dso_handle
	.ident	"GCC: (Ubuntu 7.3.0-27ubuntu1~18.04) 7.3.0"
	.section	.note.GNU-stack,"",@progbits
