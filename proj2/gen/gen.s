.text
#if(__APPLE__)
	.global _entry_point

_entry_point:
#else
	.global entry_point

entry_point:
#endif
	push %rbp	# save stack frame for C convention
	mov %rsp, %rbp

	# beginning generated code
	movq $0, %rbx
	movq %rbx, %rcx
	movq $2, %rdi
	addq %rdi, %rcx
	movq %rcx, %rbx
	movq $1, %rdi
	subq %rdi, %rcx
	movq %rcx, %rbx
	movq %rcx, %rbx
	movq %rbx, %rax
	# end generated code
	# %rax contains the result

	mov %rbp, %rsp	# reset frame
	pop %rbp
	ret



