.section .data
string_main_37:
	.asciz "\n"
string_main_36:
	.asciz "%d"
string_main_35:
	.asciz " "
string_main_34:
	.asciz "%d"
string_main_33:
	.asciz " "
string_main_32:
	.asciz "%d"
string_main_31:
	.asciz " "
string_main_30:
	.asciz "%d"
string_main_29:
	.asciz "After gurps\n"
string_main_28:
	.asciz "done b gurp\n"
string_main_27:
	.asciz "done a gurp\n"
string_main_26:
	.asciz "done y gurp\n"
string_main_25:
	.asciz "done 0z gurp\n"
string_main_24:
	.asciz "\n"
string_main_23:
	.asciz "%d"
string_main_22:
	.asciz "done z gurp\n"
string_main_21:
	.asciz "Top of loop\n"
string_gurp_20:
	.asciz "after fourth if\n"
string_gurp_19:
	.asciz "%d"
string_gurp_18:
	.asciz "%d"
string_gurp_17:
	.asciz "%d"
string_gurp_16:
	.asciz " "
string_gurp_15:
	.asciz "%d"
string_gurp_14:
	.asciz " "
string_gurp_13:
	.asciz "%d"
string_gurp_12:
	.asciz " "
string_gurp_11:
	.asciz "%d"
string_gurp_10:
	.asciz "after third if\n"
string_gurp_9:
	.asciz "after second if\n"
string_gurp_8:
	.asciz "after first if\n"
string_gurp_7:
	.asciz "after n\n"
string_gurp_6:
	.asciz "done m\n%d %d\n"
string_gurp_5:
	.asciz "done k\n"
string_gurp_4:
	.asciz "done k\n"
string_gurp_3:
	.asciz "done j\n"
string_gurp_2:
	.asciz "done i\n"
string_gurp_1:
	.asciz "done j\n"
string_gurp_0:
	.asciz "top of gurp\n"
.globl main
main:
call method_main
movq $0, %rax
ret
method_gurp:
L29: enter $0, $0  # line 3, col 7
pushq %rbx  # line 3, col 7
pushq %r12  # line 3, col 7
pushq %r13  # line 3, col 7
pushq %r14  # line 3, col 7
pushq %r15  # line 3, col 7
movq %rdi, %@local_a_1  # line 3, col 7
movq %rsi, %@local_b_2  # line 3, col 7
movq %rdx, %@local_c_3  # line 3, col 7
movq %rcx, %@local_d_4  # line 3, col 7
movq %r8, %@local_e_5  # line 3, col 7
movq %r9, %@local_f_6  # line 3, col 7
movq 16(%rbp), %@local_g_7  # line 3, col 7
movq 24(%rbp), %@local_h_8  # line 3, col 7
movq $0, %@local_i_9  # line 5, col 5
movq $0, %@local_j_10  # line 5, col 5
movq $0, %@local_k_11  # line 5, col 5
movq $0, %@local_l_12  # line 5, col 5
movq $0, %@local_m_13  # line 5, col 5
movq $0, %@local_n_14  # line 5, col 5
movq $0, %@local_o_15  # line 5, col 5
movq $0, %@local_p_16  # line 5, col 5
movq $0, %@local_q_17  # line 5, col 5
movq $0, %@local_r_18  # line 5, col 5
movq $0, %@local_s_19  # line 5, col 5
movq $0, %@local_t_20  # line 5, col 5
movq $0, %@local_u_21  # line 5, col 5
movq $0, %@local_v_22  # line 5, col 5
movq $0, %@local_w_23  # line 5, col 5
movq $0, %@local_x_24  # line 5, col 5
movq $0, %@local_y_25  # line 5, col 5
movq $0, %@local_z_26  # line 5, col 5
movq $0, %@local_a1_27  # line 5, col 5
movq $0, %@local_a2_28  # line 5, col 5
movq $0, %@local_a3_29  # line 5, col 5
movq $0, %@local_a4_30  # line 5, col 5
pushq %r10  # line 7, col 5
pushq %r11  # line 7, col 5
movq $string_gurp_0, %rdi  # line 7, col 5
movq $0, %rax  # line 7, col 5
call printf  # line 7, col 5
popq %r11  # line 7, col 5
popq %r10  # line 7, col 5
movq %rax, %@temp_31  # line 7, col 5
movq %@local_a_1, %@s_283  # line 8, col 9
imulq %@local_b_2, %@s_283  # line 8, col 9
movq %@s_283, %@s_284  # line 8, col 9
subq %@local_e_5, %@s_284  # line 8, col 9
movq %@s_284, %@s_285  # line 8, col 9
addq %@local_d_4, %@s_285  # line 8, col 9
movq %@s_285, %@local_j_10  # line 8, col 5
pushq %r10  # line 9, col 5
pushq %r11  # line 9, col 5
movq $string_gurp_1, %rdi  # line 9, col 5
movq $0, %rax  # line 9, col 5
call printf  # line 9, col 5
popq %r11  # line 9, col 5
popq %r10  # line 9, col 5
movq %rax, %@temp_32  # line 9, col 5
movq %@local_j_10, %@s_289  # line 10, col 9
subq $1, %@s_289  # line 10, col 9
movq %@s_289, %@local_i_9  # line 10, col 5
pushq %r10  # line 11, col 5
pushq %r11  # line 11, col 5
movq $string_gurp_2, %rdi  # line 11, col 5
movq $0, %rax  # line 11, col 5
call printf  # line 11, col 5
popq %r11  # line 11, col 5
popq %r10  # line 11, col 5
movq %rax, %@temp_33  # line 11, col 5
movq $3, %@s_295  # line 12, col 9
addq %@local_i_9, %@s_295  # line 12, col 9
movq %@s_295, %@local_j_10  # line 12, col 5
pushq %r10  # line 13, col 5
pushq %r11  # line 13, col 5
movq $string_gurp_3, %rdi  # line 13, col 5
movq $0, %rax  # line 13, col 5
call printf  # line 13, col 5
popq %r11  # line 13, col 5
popq %r10  # line 13, col 5
movq %rax, %@temp_34  # line 13, col 5
movq %@local_i_9, %@s_299  # line 14, col 9
addq %@local_j_10, %@s_299  # line 14, col 9
movq %@s_299, %@s_302  # line 14, col 9
subq $2, %@s_302  # line 14, col 9
movq %@s_302, %@local_k_11  # line 14, col 5
pushq %r10  # line 15, col 5
pushq %r11  # line 15, col 5
movq $string_gurp_4, %rdi  # line 15, col 5
movq $0, %rax  # line 15, col 5
call printf  # line 15, col 5
popq %r11  # line 15, col 5
popq %r10  # line 15, col 5
movq %rax, %@temp_35  # line 15, col 5
movq %@local_k_11, %@s_306  # line 16, col 9
subq %@local_j_10, %@s_306  # line 16, col 9
movq %@s_306, %@local_l_12  # line 16, col 5
pushq %r10  # line 17, col 5
pushq %r11  # line 17, col 5
movq $string_gurp_5, %rdi  # line 17, col 5
movq $0, %rax  # line 17, col 5
call printf  # line 17, col 5
popq %r11  # line 17, col 5
popq %r10  # line 17, col 5
movq %rax, %@temp_36  # line 17, col 5
movq %@local_i_9, %@s_308  # line 18, col 9
addq %@local_k_11, %@s_308  # line 18, col 9
movq %@s_308, %@local_m_13  # line 18, col 5
pushq %r10  # line 19, col 5
pushq %r11  # line 19, col 5
movq %@local_m_13, %rdx  # line 19, col 5
movq %@local_k_11, %rsi  # line 19, col 5
movq $string_gurp_6, %rdi  # line 19, col 5
movq $0, %rax  # line 19, col 5
call printf  # line 19, col 5
popq %r11  # line 19, col 5
popq %r10  # line 19, col 5
movq %rax, %@temp_37  # line 19, col 5
movq %@local_i_9, %@s_312  # line 20, col 9
movq %@local_j_10, %@s_311  # line 20, col 14
movq %@local_k_11, %@s_310  # line 20, col 19
subq %@local_m_13, %@s_310  # line 20, col 19
subq %@s_310, %@s_311  # line 20, col 14
addq %@s_311, %@s_312  # line 20, col 9
movq %@s_312, %@local_n_14  # line 20, col 5
pushq %r10  # line 21, col 5
pushq %r11  # line 21, col 5
movq $string_gurp_7, %rdi  # line 21, col 5
movq $0, %rax  # line 21, col 5
call printf  # line 21, col 5
popq %r11  # line 21, col 5
popq %r10  # line 21, col 5
movq %rax, %@temp_38  # line 21, col 5
cmpq $50, %@local_a_1  # line 22, col 10
jg L1  # line 22, col 5 falls to L2
L2:  # line 22, col 5
movq %@local_b_2, %@s_4  # line 43, col 13
subq %@local_a_1, %@s_4  # line 43, col 13
movq %@s_4, %@local_o_15  # line 43, col 9
movq %@local_l_12, %@s_5  # line 44, col 13
addq %@local_m_13, %@s_5  # line 44, col 13
movq %@s_5, %@local_j_10  # line 44, col 9
cmpq $0, %@local_g_7  # line -1, col -1
jne L13  # line 45, col 9 falls to L14
L14:  # line 45, col 9
movq $3, %@s_65  # line 53, col 17
movq %@local_o_15, %@s_59  # line 53, col 22
subq %@local_a_1, %@s_59  # line 53, col 22
movq %@s_59, %@s_62  # line 53, col 22
subq $2, %@s_62  # line 53, col 22
addq %@s_62, %@s_65  # line 53, col 17
movq %@s_65, %@local_s_19  # line 53, col 13
movq %@local_s_19, %@s_86  # line 54, col 17
addq %@local_j_10, %@s_86  # line 54, col 17
movq %@s_86, %@local_q_17  # line 54, col 13
movq %@local_s_19, %@s_87  # line 55, col 17
addq %@local_q_17, %@s_87  # line 55, col 17
movq %@s_87, %@s_88  # line 55, col 17
subq %@local_q_17, %@s_88  # line 55, col 17
movq %@s_88, %@local_f_6  # line 55, col 13
jmp L15  # line 45, col 9
L15:  # line 45, col 9
jmp L3  # line 22, col 5
L3:  # line 22, col 5
pushq %r10  # line 58, col 5
pushq %r11  # line 58, col 5
movq $string_gurp_8, %rdi  # line 58, col 5
movq $0, %rax  # line 58, col 5
call printf  # line 58, col 5
popq %r11  # line 58, col 5
popq %r10  # line 58, col 5
movq %rax, %@temp_40  # line 58, col 5
movq %@local_e_5, %@s_7  # line 59, col 9
addq %@local_l_12, %@s_7  # line 59, col 9
movq %@s_7, %@s_8  # line 59, col 9
subq %@local_i_9, %@s_8  # line 59, col 9
movq %@s_8, %@local_t_20  # line 59, col 5
movq %@local_t_20, %@s_9  # line 60, col 10
addq %@local_j_10, %@s_9  # line 60, col 10
movq %@s_9, %@s_10  # line 60, col 10
addq %@local_o_15, %@s_10  # line 60, col 10
movq %@s_10, %@local_a1_27  # line 60, col 5
movq %@local_t_20, %@s_11  # line 61, col 9
subq %@local_a1_27, %@s_11  # line 61, col 9
movq %@s_11, %@s_12  # line 61, col 9
addq %@local_m_13, %@s_12  # line 61, col 9
movq %@s_12, %@s_13  # line 61, col 9
subq %@local_j_10, %@s_13  # line 61, col 9
movq %@s_13, %@local_r_18  # line 61, col 5
movq %@local_l_12, %@s_14  # line 62, col 9
addq %@local_a1_27, %@s_14  # line 62, col 9
movq %@s_14, %@s_17  # line 62, col 9
movq %@local_t_20, %@s_16  # line 62, col 19
movq %@local_q_17, %@s_15  # line 62, col 24
addq %@local_f_6, %@s_15  # line 62, col 24
subq %@s_15, %@s_16  # line 62, col 19
addq %@s_16, %@s_17  # line 62, col 9
movq %@s_17, %@local_v_22  # line 62, col 5
cmpq $0, %@local_g_7  # line -1, col -1
jne L16  # line 63, col 5 falls to L17
L17:  # line 63, col 5
movq $-1, %@local_w_23  # line 69, col 9
jmp L18  # line 63, col 5
L18:  # line 63, col 5
pushq %r10  # line 71, col 5
pushq %r11  # line 71, col 5
movq $string_gurp_9, %rdi  # line 71, col 5
movq $0, %rax  # line 71, col 5
call printf  # line 71, col 5
popq %r11  # line 71, col 5
popq %r10  # line 71, col 5
movq %rax, %@temp_41  # line 71, col 5
movq $99, %@s_96  # line 72, col 9
addq %@local_n_14, %@s_96  # line 72, col 9
movq %@s_96, %@s_99  # line 72, col 9
subq %@local_e_5, %@s_99  # line 72, col 9
movq %@s_99, %@s_102  # line 72, col 9
addq %@local_t_20, %@s_102  # line 72, col 9
movq %@s_102, %@local_u_21  # line 72, col 5
movq %@local_e_5, %@s_105  # line 73, col 9
subq %@local_s_19, %@s_105  # line 73, col 9
movq %@s_105, %@s_106  # line 73, col 9
addq %@local_n_14, %@s_106  # line 73, col 9
movq %@s_106, %@s_107  # line 73, col 9
addq %@local_o_15, %@s_107  # line 73, col 9
movq %@s_107, %@s_108  # line 73, col 9
addq %@local_m_13, %@s_108  # line 73, col 9
movq %@s_108, %@s_109  # line 73, col 9
subq %@local_e_5, %@s_109  # line 73, col 9
movq %@s_109, %@s_110  # line 73, col 9
addq %@local_b_2, %@s_110  # line 73, col 9
movq %@s_110, %@s_111  # line 73, col 9
subq %@local_b_2, %@s_111  # line 73, col 9
movq %@s_111, %@s_112  # line 73, col 9
addq %@local_e_5, %@s_112  # line 73, col 9
movq %@s_112, %@local_y_25  # line 73, col 5
movq %@local_a1_27, %@s_113  # line 74, col 10
addq %@local_t_20, %@s_113  # line 74, col 10
movq %@s_113, %@s_114  # line 74, col 10
subq %@local_n_14, %@s_114  # line 74, col 10
movq %@s_114, %@s_115  # line 74, col 10
subq %@local_t_20, %@s_115  # line 74, col 10
movq %@s_115, %@local_a2_28  # line 74, col 5
movq %@local_h_8, %@s_116  # line 75, col 10
addq %@local_f_6, %@s_116  # line 75, col 10
movq %@s_116, %@s_117  # line 75, col 10
addq %@local_d_4, %@s_117  # line 75, col 10
movq %@s_117, %@s_118  # line 75, col 10
subq %@local_e_5, %@s_118  # line 75, col 10
movq %@s_118, %@local_a4_30  # line 75, col 5
cmpq $-1, %@local_w_23  # line 76, col 10
je L19  # line 76, col 5 falls to L20
L20:  # line 76, col 5
movq %@local_a4_30, %@s_130  # line 82, col 14
subq %@local_a2_28, %@s_130  # line 82, col 14
movq %@s_130, %@local_a3_29  # line 82, col 9
jmp L21  # line 76, col 5
L21:  # line 76, col 5
movq %@local_u_21, %@s_131  # line 84, col 9
subq %@local_v_22, %@s_131  # line 84, col 9
movq %@s_131, %@s_132  # line 84, col 9
addq %@local_w_23, %@s_132  # line 84, col 9
movq %@s_132, %@local_z_26  # line 84, col 5
movq $42, %@s_135  # line 85, col 9
subq %@local_z_26, %@s_135  # line 85, col 9
movq %@s_135, %@local_p_16  # line 85, col 5
pushq %r10  # line 87, col 5
pushq %r11  # line 87, col 5
movq $string_gurp_10, %rdi  # line 87, col 5
movq $0, %rax  # line 87, col 5
call printf  # line 87, col 5
popq %r11  # line 87, col 5
popq %r10  # line 87, col 5
movq %rax, %@temp_42  # line 87, col 5
movq %@local_a_1, %@s_140  # line 88, col 27
subq %@local_i_9, %@s_140  # line 88, col 27
movq %@s_140, %@s_141  # line 88, col 27
addq %@local_d_4, %@s_141  # line 88, col 27
movq %@s_141, %@s_142  # line 88, col 27
addq %@local_j_10, %@s_142  # line 88, col 27
movq %@s_142, %@s_143  # line 88, col 27
subq %@local_e_5, %@s_143  # line 88, col 27
movq %@s_143, %@s_144  # line 88, col 27
subq %@local_f_6, %@s_144  # line 88, col 27
movq %@s_144, %@s_145  # line 88, col 27
addq %@local_l_12, %@s_145  # line 88, col 27
movq %@s_145, %@s_146  # line 88, col 27
addq %@local_m_13, %@s_146  # line 88, col 27
pushq %r10  # line 88, col 5
pushq %r11  # line 88, col 5
movq %@s_146, %rsi  # line 88, col 5
movq $string_gurp_11, %rdi  # line 88, col 5
movq $0, %rax  # line 88, col 5
call printf  # line 88, col 5
popq %r11  # line 88, col 5
popq %r10  # line 88, col 5
movq %rax, %@temp_43  # line 88, col 5
pushq %r10  # line 89, col 5
pushq %r11  # line 89, col 5
movq $string_gurp_12, %rdi  # line 89, col 5
movq $0, %rax  # line 89, col 5
call printf  # line 89, col 5
popq %r11  # line 89, col 5
popq %r10  # line 89, col 5
movq %rax, %@temp_44  # line 89, col 5
movq %@local_b_2, %@s_156  # line 90, col 27
subq %@local_k_11, %@s_156  # line 90, col 27
movq %@s_156, %@s_157  # line 90, col 27
subq %@local_h_8, %@s_157  # line 90, col 27
movq %@s_157, %@s_158  # line 90, col 27
addq %@local_n_14, %@s_158  # line 90, col 27
movq %@s_158, %@s_159  # line 90, col 27
addq %@local_o_15, %@s_159  # line 90, col 27
movq %@s_159, %@s_160  # line 90, col 27
addq %@local_q_17, %@s_160  # line 90, col 27
movq %@s_160, %@s_161  # line 90, col 27
subq %@local_r_18, %@s_161  # line 90, col 27
movq %@s_161, %@s_162  # line 90, col 27
subq %@local_a2_28, %@s_162  # line 90, col 27
pushq %r10  # line 90, col 5
pushq %r11  # line 90, col 5
movq %@s_162, %rsi  # line 90, col 5
movq $string_gurp_13, %rdi  # line 90, col 5
movq $0, %rax  # line 90, col 5
call printf  # line 90, col 5
popq %r11  # line 90, col 5
popq %r10  # line 90, col 5
movq %rax, %@temp_45  # line 90, col 5
pushq %r10  # line 91, col 5
pushq %r11  # line 91, col 5
movq $string_gurp_14, %rdi  # line 91, col 5
movq $0, %rax  # line 91, col 5
call printf  # line 91, col 5
popq %r11  # line 91, col 5
popq %r10  # line 91, col 5
movq %rax, %@temp_46  # line 91, col 5
movq %@local_a4_30, %@s_172  # line 92, col 27
addq %@local_s_19, %@s_172  # line 92, col 27
movq %@s_172, %@s_173  # line 92, col 27
subq %@local_t_20, %@s_173  # line 92, col 27
movq %@s_173, %@s_174  # line 92, col 27
addq %@local_z_26, %@s_174  # line 92, col 27
movq %@s_174, %@s_175  # line 92, col 27
subq %@local_y_25, %@s_175  # line 92, col 27
movq %@s_175, %@s_176  # line 92, col 27
addq %@local_x_24, %@s_176  # line 92, col 27
movq %@s_176, %@s_177  # line 92, col 27
addq %@local_w_23, %@s_177  # line 92, col 27
movq %@s_177, %@s_178  # line 92, col 27
subq %@local_a3_29, %@s_178  # line 92, col 27
pushq %r10  # line 92, col 5
pushq %r11  # line 92, col 5
movq %@s_178, %rsi  # line 92, col 5
movq $string_gurp_15, %rdi  # line 92, col 5
movq $0, %rax  # line 92, col 5
call printf  # line 92, col 5
popq %r11  # line 92, col 5
popq %r10  # line 92, col 5
movq %rax, %@temp_47  # line 92, col 5
pushq %r10  # line 93, col 5
pushq %r11  # line 93, col 5
movq $string_gurp_16, %rdi  # line 93, col 5
movq $0, %rax  # line 93, col 5
call printf  # line 93, col 5
popq %r11  # line 93, col 5
popq %r10  # line 93, col 5
movq %rax, %@temp_48  # line 93, col 5
cmpq $0, %@local_c_3  # line -1, col -1
jne L22  # line 94, col 5 falls to L23
L23:  # line 94, col 5
cmpq $0, %@local_g_7  # line -1, col -1
jne L25  # line 100, col 9 falls to L26
L26:  # line 100, col 9
movq %@local_a1_27, %@s_230  # line 106, col 35
addq %@local_v_22, %@s_230  # line 106, col 35
movq %@s_230, %@s_231  # line 106, col 35
addq %@local_p_16, %@s_231  # line 106, col 35
movq %@s_231, %@s_232  # line 106, col 35
subq %@local_u_21, %@s_232  # line 106, col 35
pushq %r10  # line 106, col 13
pushq %r11  # line 106, col 13
movq %@s_232, %rsi  # line 106, col 13
movq $string_gurp_19, %rdi  # line 106, col 13
movq $0, %rax  # line 106, col 13
call printf  # line 106, col 13
popq %r11  # line 106, col 13
popq %r10  # line 106, col 13
movq %rax, %@temp_51  # line 106, col 13
jmp L27  # line 100, col 9
L27:  # line 100, col 9
jmp L24  # line 94, col 5
L24:  # line 94, col 5
pushq %r10  # line 109, col 5
pushq %r11  # line 109, col 5
movq $string_gurp_20, %rdi  # line 109, col 5
movq $0, %rax  # line 109, col 5
call printf  # line 109, col 5
popq %r11  # line 109, col 5
popq %r10  # line 109, col 5
movq %rax, %@temp_52  # line 109, col 5
movq %@local_a_1, %@s_195  # line 110, col 12
subq %@local_b_2, %@s_195  # line 110, col 12
movq %@s_195, %@s_196  # line 110, col 12
addq %@local_d_4, %@s_196  # line 110, col 12
movq %@s_196, %@s_197  # line 110, col 12
addq %@local_e_5, %@s_197  # line 110, col 12
movq %@s_197, %@s_198  # line 110, col 12
addq %@local_f_6, %@s_198  # line 110, col 12
movq %@s_198, %@s_199  # line 110, col 12
addq %@local_h_8, %@s_199  # line 110, col 12
movq %@s_199, %@s_200  # line 110, col 12
addq %@local_i_9, %@s_200  # line 110, col 12
movq %@s_200, %@s_201  # line 110, col 12
addq %@local_j_10, %@s_201  # line 110, col 12
movq %@s_201, %@s_202  # line 110, col 12
addq %@local_k_11, %@s_202  # line 110, col 12
movq %@s_202, %@s_203  # line 110, col 12
addq %@local_l_12, %@s_203  # line 110, col 12
movq %@s_203, %@s_204  # line 110, col 12
addq %@local_m_13, %@s_204  # line 110, col 12
movq %@s_204, %@s_205  # line 110, col 12
subq %@local_n_14, %@s_205  # line 110, col 12
movq %@s_205, %@s_206  # line 110, col 12
addq %@local_o_15, %@s_206  # line 110, col 12
movq %@s_206, %@s_207  # line 110, col 12
subq %@local_p_16, %@s_207  # line 110, col 12
movq %@s_207, %@s_208  # line 110, col 12
addq %@local_q_17, %@s_208  # line 110, col 12
movq %@s_208, %@s_209  # line 110, col 12
subq %@local_r_18, %@s_209  # line 110, col 12
movq %@s_209, %@s_210  # line 110, col 12
addq %@local_s_19, %@s_210  # line 110, col 12
movq %@s_210, %@s_211  # line 110, col 12
subq %@local_t_20, %@s_211  # line 110, col 12
movq %@s_211, %@s_212  # line 110, col 12
addq %@local_u_21, %@s_212  # line 110, col 12
movq %@s_212, %@s_213  # line 110, col 12
subq %@local_v_22, %@s_213  # line 110, col 12
movq %@s_213, %@s_214  # line 110, col 12
addq %@local_w_23, %@s_214  # line 110, col 12
movq %@s_214, %@s_215  # line 110, col 12
subq %@local_x_24, %@s_215  # line 110, col 12
movq %@s_215, %@s_216  # line 110, col 12
addq %@local_y_25, %@s_216  # line 110, col 12
movq %@s_216, %@s_217  # line 110, col 12
subq %@local_z_26, %@s_217  # line 110, col 12
movq %@s_217, %@s_218  # line 110, col 12
addq %@local_a1_27, %@s_218  # line 110, col 12
movq %@s_218, %@s_219  # line 110, col 12
addq %@local_a2_28, %@s_219  # line 110, col 12
movq %@s_219, %@s_220  # line 110, col 12
addq %@local_a3_29, %@s_220  # line 110, col 12
movq %@s_220, %@s_221  # line 110, col 12
subq %@local_a4_30, %@s_221  # line 110, col 12
movq %@s_221, %rax  # line 110, col 5
popq %r15  # line 110, col 5
popq %r14  # line 110, col 5
popq %r13  # line 110, col 5
popq %r12  # line 110, col 5
popq %rbx  # line 110, col 5
leave  # line 110, col 5
ret  # line 110, col 5
L25:  # line 100, col 9
movq %@local_u_21, %@s_223  # line 102, col 35
subq %@local_v_22, %@s_223  # line 102, col 35
movq %@s_223, %@s_224  # line 102, col 35
addq %@local_a1_27, %@s_224  # line 102, col 35
movq %@s_224, %@s_225  # line 102, col 35
subq %@local_p_16, %@s_225  # line 102, col 35
pushq %r10  # line 102, col 13
pushq %r11  # line 102, col 13
movq %@s_225, %rsi  # line 102, col 13
movq $string_gurp_18, %rdi  # line 102, col 13
movq $0, %rax  # line 102, col 13
call printf  # line 102, col 13
popq %r11  # line 102, col 13
popq %r10  # line 102, col 13
movq %rax, %@temp_50  # line 102, col 13
jmp L27  # line 100, col 9
L22:  # line 94, col 5
movq %@local_p_16, %@s_188  # line 96, col 31
addq %@local_u_21, %@s_188  # line 96, col 31
movq %@s_188, %@s_189  # line 96, col 31
subq %@local_v_22, %@s_189  # line 96, col 31
movq %@s_189, %@s_190  # line 96, col 31
addq %@local_a1_27, %@s_190  # line 96, col 31
pushq %r10  # line 96, col 9
pushq %r11  # line 96, col 9
movq %@s_190, %rsi  # line 96, col 9
movq $string_gurp_17, %rdi  # line 96, col 9
movq $0, %rax  # line 96, col 9
call printf  # line 96, col 9
popq %r11  # line 96, col 9
popq %r10  # line 96, col 9
movq %rax, %@temp_49  # line 96, col 9
jmp L24  # line 94, col 5
L19:  # line 76, col 5
movq %@local_a2_28, %@s_129  # line 78, col 14
addq %@local_a4_30, %@s_129  # line 78, col 14
movq %@s_129, %@local_a3_29  # line 78, col 9
jmp L21  # line 76, col 5
L16:  # line 63, col 5
movq $3, %@local_w_23  # line 65, col 9
jmp L18  # line 63, col 5
L13:  # line 45, col 9
movq $3, %@s_46  # line 47, col 17
movq %@local_a_1, %@s_45  # line 47, col 22
subq %@local_o_15, %@s_45  # line 47, col 22
addq %@s_45, %@s_46  # line 47, col 17
movq %@s_46, %@local_f_6  # line 47, col 13
movq $3, %@s_53  # line 48, col 17
subq %@local_o_15, %@s_53  # line 48, col 17
movq %@s_53, %@local_q_17  # line 48, col 13
movq %@local_f_6, %@s_56  # line 49, col 17
addq %@local_q_17, %@s_56  # line 49, col 17
movq %@s_56, %@local_s_19  # line 49, col 13
jmp L15  # line 45, col 9
L1:  # line 22, col 5
movq %@local_a_1, %@s_1  # line 24, col 13
addq %@local_b_2, %@s_1  # line 24, col 13
movq %@s_1, %@s_2  # line 24, col 13
addq %@local_l_12, %@s_2  # line 24, col 13
movq %@s_2, %@local_o_15  # line 24, col 9
movq %@local_l_12, %@s_3  # line 25, col 13
subq %@local_m_13, %@s_3  # line 25, col 13
movq %@s_3, %@local_j_10  # line 25, col 9
cmpq $0, %@local_c_3  # line -1, col -1
jne L4  # line 26, col 9 falls to L5
L5:  # line 26, col 9
movq %@local_o_15, %@s_33  # line 34, col 17
addq $3, %@s_33  # line 34, col 17
movq %@s_33, %@local_q_17  # line 34, col 13
jmp L6  # line 26, col 9
L6:  # line 26, col 9
movq $-1, %@temp_39  # line 36, col 14
cmpq $0, %@local_c_3  # line -1, col -1
jne L12  # line 36, col 14 falls to L10
L10:  # line 36, col 14
cmpq $0, %@local_g_7  # line -1, col -1
jne L12  # line 36, col 14 falls to L11
L11:  # line 36, col 14
movq $0, %@temp_39  # line 36, col 14
jmp L12  # line 36, col 14
L12:  # line 36, col 14
cmpq $0, %@temp_39  # line -1, col -1
jne L7  # line 36, col 9 falls to L8
L8:  # line 36, col 9
jmp L9  # line 36, col 9
L9:  # line 36, col 9
jmp L3  # line 22, col 5
L7:  # line 36, col 9
movq %@local_f_6, %@s_38  # line 38, col 17
addq %@local_e_5, %@s_38  # line 38, col 17
movq %@s_38, %@s_40  # line 38, col 17
movq %@local_h_8, %@s_39  # line 38, col 26
subq %@local_b_2, %@s_39  # line 38, col 26
addq %@s_39, %@s_40  # line 38, col 17
movq %@s_40, %@local_s_19  # line 38, col 13
jmp L9  # line 36, col 9
L4:  # line 26, col 9
movq %@local_e_5, %@s_18  # line 28, col 17
addq %@local_f_6, %@s_18  # line 28, col 17
movq %@s_18, %@s_20  # line 28, col 17
movq %@local_h_8, %@s_19  # line 28, col 26
addq %@local_n_14, %@s_19  # line 28, col 26
subq %@s_19, %@s_20  # line 28, col 17
movq %@s_20, %@local_l_12  # line 28, col 13
movq %@local_f_6, %@s_23  # line 29, col 17
subq $1, %@s_23  # line 29, col 17
movq %@s_23, %@local_f_6  # line 29, col 13
movq %@local_o_15, %@s_28  # line 30, col 17
subq $3, %@s_28  # line 30, col 17
movq %@s_28, %@local_q_17  # line 30, col 13
jmp L6  # line 26, col 9
method_main:
L34: enter $0, $0  # line 115, col 8
pushq %rbx  # line 115, col 8
pushq %r12  # line 115, col 8
pushq %r13  # line 115, col 8
pushq %r14  # line 115, col 8
pushq %r15  # line 115, col 8
movq $0, %@local_y_53  # line 117, col 5
movq $0, %@local_z_54  # line 117, col 5
movq $0, %@local_a_55  # line 117, col 5
movq $0, %@local_b_56  # line 117, col 5
movq $0, %@local_x_57  # line 118, col 5
movq $3, %@local_x_59  # line 119, col 5
movq $5, %@temp_58  # line 119, col 5
jmp L30  # line 119, col 5
L30:  # line 119, col 5
cmpq %@temp_58, %@local_x_59  # line 119, col 5
jl L31  # line 119, col 5 falls to L33
L33:  # line 119, col 5
popq %r15  # line 115, col 8
popq %r14  # line 115, col 8
popq %r13  # line 115, col 8
popq %r12  # line 115, col 8
popq %rbx  # line 115, col 8
leave  # line 115, col 8
ret  # line 115, col 8 (void)
L31:  # line 119, col 5
pushq %r10  # line 121, col 9
pushq %r11  # line 121, col 9
movq $string_main_21, %rdi  # line 121, col 9
movq $0, %rax  # line 121, col 9
call printf  # line 121, col 9
popq %r11  # line 121, col 9
popq %r10  # line 121, col 9
movq %rax, %@temp_60  # line 121, col 9
movq $1, %@s_329  # line 122, col 18
addq %@local_x_59, %@s_329  # line 122, col 18
movq $0, %@s_334  # line 122, col 25
subq %@local_x_59, %@s_334  # line 122, col 25
movq $2, %@s_343  # line 122, col 39
addq %@local_x_59, %@s_343  # line 122, col 39
movq $1, %@s_348  # line 122, col 46
subq %@local_x_59, %@s_348  # line 122, col 46
movq $4, %@s_355  # line 122, col 59
subq %@local_x_59, %@s_355  # line 122, col 59
pushq %r10  # line 122, col 13
pushq %r11  # line 122, col 13
pushq %@s_355  # line 122, col 13
pushq $-1  # line 122, col 13
movq %@s_348, %r9  # line 122, col 13
movq %@s_343, %r8  # line 122, col 13
movq $3, %rcx  # line 122, col 13
movq $-1, %rdx  # line 122, col 13
movq %@s_334, %rsi  # line 122, col 13
movq %@s_329, %rdi  # line 122, col 13
call method_gurp  # line 122, col 13
addq $16, %rsp  # line 122, col 13
popq %r11  # line 122, col 13
popq %r10  # line 122, col 13
movq %rax, %@temp_61  # line 122, col 13
movq %@temp_61, %@local_z_54  # line 122, col 9
pushq %r10  # line 123, col 9
pushq %r11  # line 123, col 9
movq $string_main_22, %rdi  # line 123, col 9
movq $0, %rax  # line 123, col 9
call printf  # line 123, col 9
popq %r11  # line 123, col 9
popq %r10  # line 123, col 9
movq %rax, %@temp_62  # line 123, col 9
pushq %r10  # line 124, col 9
pushq %r11  # line 124, col 9
movq %@local_x_59, %rsi  # line 124, col 9
movq $string_main_23, %rdi  # line 124, col 9
movq $0, %rax  # line 124, col 9
call printf  # line 124, col 9
popq %r11  # line 124, col 9
popq %r10  # line 124, col 9
movq %rax, %@temp_63  # line 124, col 9
pushq %r10  # line 125, col 9
pushq %r11  # line 125, col 9
movq $string_main_24, %rdi  # line 125, col 9
movq $0, %rax  # line 125, col 9
call printf  # line 125, col 9
popq %r11  # line 125, col 9
popq %r10  # line 125, col 9
movq %rax, %@temp_64  # line 125, col 9
movq $1, %@s_14437  # line 126, col 18
addq %@local_x_59, %@s_14437  # line 126, col 18
movq $0, %@s_14442  # line 126, col 25
subq %@local_x_59, %@s_14442  # line 126, col 25
movq $2, %@s_14451  # line 126, col 39
addq %@local_x_59, %@s_14451  # line 126, col 39
movq %@local_x_59, %@s_14456  # line 126, col 46
addq $1, %@s_14456  # line 126, col 46
pushq %r10  # line 126, col 13
pushq %r11  # line 126, col 13
pushq $0  # line 126, col 13
pushq $-1  # line 126, col 13
movq %@s_14456, %r9  # line 126, col 13
movq %@s_14451, %r8  # line 126, col 13
movq $3, %rcx  # line 126, col 13
movq $-1, %rdx  # line 126, col 13
movq %@s_14442, %rsi  # line 126, col 13
movq %@s_14437, %rdi  # line 126, col 13
call method_gurp  # line 126, col 13
addq $16, %rsp  # line 126, col 13
popq %r11  # line 126, col 13
popq %r10  # line 126, col 13
movq %rax, %@temp_65  # line 126, col 13
movq %@temp_65, %@local_z_54  # line 126, col 9
pushq %r10  # line 127, col 9
pushq %r11  # line 127, col 9
movq $string_main_25, %rdi  # line 127, col 9
movq $0, %rax  # line 127, col 9
call printf  # line 127, col 9
popq %r11  # line 127, col 9
popq %r10  # line 127, col 9
movq %rax, %@temp_66  # line 127, col 9
movq $3, %@s_21982  # line 128, col 18
subq %@local_x_59, %@s_21982  # line 128, col 18
movq $-8, %@s_21987  # line 128, col 25
addq %@local_x_59, %@s_21987  # line 128, col 25
movq $12, %@s_21999  # line 128, col 40
movq $3, %@s_21996  # line 128, col 45
imulq %@local_x_59, %@s_21996  # line 128, col 45
subq %@s_21996, %@s_21999  # line 128, col 40
movq $16, %@s_22020  # line 128, col 52
addq %@local_x_59, %@s_22020  # line 128, col 52
movq $8, %@s_22029  # line 128, col 69
subq %@local_x_59, %@s_22029  # line 128, col 69
pushq %r10  # line 128, col 13
pushq %r11  # line 128, col 13
pushq %@s_22029  # line 128, col 13
pushq $-1  # line 128, col 13
movq $1, %r9  # line 128, col 13
movq %@s_22020, %r8  # line 128, col 13
movq %@s_21999, %rcx  # line 128, col 13
movq $0, %rdx  # line 128, col 13
movq %@s_21987, %rsi  # line 128, col 13
movq %@s_21982, %rdi  # line 128, col 13
call method_gurp  # line 128, col 13
addq $16, %rsp  # line 128, col 13
popq %r11  # line 128, col 13
popq %r10  # line 128, col 13
movq %rax, %@temp_67  # line 128, col 13
movq %@temp_67, %@local_y_53  # line 128, col 9
pushq %r10  # line 129, col 9
pushq %r11  # line 129, col 9
movq $string_main_26, %rdi  # line 129, col 9
movq $0, %rax  # line 129, col 9
call printf  # line 129, col 9
popq %r11  # line 129, col 9
popq %r10  # line 129, col 9
movq %rax, %@temp_68  # line 129, col 9
movq $2, %@s_62575  # line 130, col 18
subq %@local_x_59, %@s_62575  # line 130, col 18
movq $6, %@s_62580  # line 130, col 25
addq %@local_x_59, %@s_62580  # line 130, col 25
imulq $-3, %@local_x_59, %@s_62585  # line 130, col 39
movq $3, %@s_62599  # line 130, col 50
imulq $2, %@local_x_59, %@s_62594  # line 130, col 54
subq %@s_62594, %@s_62599  # line 130, col 50
movq $5, %@s_62622  # line 130, col 68
subq %@local_x_59, %@s_62622  # line 130, col 68
pushq %r10  # line 130, col 13
pushq %r11  # line 130, col 13
pushq %@s_62622  # line 130, col 13
pushq $0  # line 130, col 13
movq %@s_62599, %r9  # line 130, col 13
movq $1, %r8  # line 130, col 13
movq %@s_62585, %rcx  # line 130, col 13
movq $0, %rdx  # line 130, col 13
movq %@s_62580, %rsi  # line 130, col 13
movq %@s_62575, %rdi  # line 130, col 13
call method_gurp  # line 130, col 13
addq $16, %rsp  # line 130, col 13
popq %r11  # line 130, col 13
popq %r10  # line 130, col 13
movq %rax, %@temp_69  # line 130, col 13
movq %@temp_69, %@local_a_55  # line 130, col 9
pushq %r10  # line 131, col 9
pushq %r11  # line 131, col 9
movq $string_main_27, %rdi  # line 131, col 9
movq $0, %rax  # line 131, col 9
call printf  # line 131, col 9
popq %r11  # line 131, col 9
popq %r10  # line 131, col 9
movq %rax, %@temp_70  # line 131, col 9
movq $7, %@s_106414  # line 132, col 31
subq %@local_x_59, %@s_106414  # line 132, col 31
movq %@local_x_59, %@s_106419  # line 132, col 38
subq $4, %@s_106419  # line 132, col 38
movq $6, %@s_106433  # line 132, col 55
imulq $9, %@local_x_59, %@s_106428  # line 132, col 59
subq %@s_106428, %@s_106433  # line 132, col 55
pushq %r10  # line 132, col 13
pushq %r11  # line 132, col 13
pushq %@s_106433  # line 132, col 13
pushq $0  # line 132, col 13
movq $2, %r9  # line 132, col 13
movq %@s_106419, %r8  # line 132, col 13
movq %@s_106414, %rcx  # line 132, col 13
movq $-1, %rdx  # line 132, col 13
movq $8, %rsi  # line 132, col 13
movq $-3, %rdi  # line 132, col 13
call method_gurp  # line 132, col 13
addq $16, %rsp  # line 132, col 13
popq %r11  # line 132, col 13
popq %r10  # line 132, col 13
movq %rax, %@temp_71  # line 132, col 13
movq %@temp_71, %@local_b_56  # line 132, col 9
pushq %r10  # line 133, col 9
pushq %r11  # line 133, col 9
movq $string_main_28, %rdi  # line 133, col 9
movq $0, %rax  # line 133, col 9
call printf  # line 133, col 9
popq %r11  # line 133, col 9
popq %r10  # line 133, col 9
movq %rax, %@temp_72  # line 133, col 9
pushq %r10  # line 134, col 9
pushq %r11  # line 134, col 9
movq $string_main_29, %rdi  # line 134, col 9
movq $0, %rax  # line 134, col 9
call printf  # line 134, col 9
popq %r11  # line 134, col 9
popq %r10  # line 134, col 9
movq %rax, %@temp_73  # line 134, col 9
pushq %r10  # line 135, col 9
pushq %r11  # line 135, col 9
movq %@local_y_53, %rsi  # line 135, col 9
movq $string_main_30, %rdi  # line 135, col 9
movq $0, %rax  # line 135, col 9
call printf  # line 135, col 9
popq %r11  # line 135, col 9
popq %r10  # line 135, col 9
movq %rax, %@temp_74  # line 135, col 9
pushq %r10  # line 136, col 9
pushq %r11  # line 136, col 9
movq $string_main_31, %rdi  # line 136, col 9
movq $0, %rax  # line 136, col 9
call printf  # line 136, col 9
popq %r11  # line 136, col 9
popq %r10  # line 136, col 9
movq %rax, %@temp_75  # line 136, col 9
pushq %r10  # line 137, col 9
pushq %r11  # line 137, col 9
movq %@local_z_54, %rsi  # line 137, col 9
movq $string_main_32, %rdi  # line 137, col 9
movq $0, %rax  # line 137, col 9
call printf  # line 137, col 9
popq %r11  # line 137, col 9
popq %r10  # line 137, col 9
movq %rax, %@temp_76  # line 137, col 9
pushq %r10  # line 138, col 9
pushq %r11  # line 138, col 9
movq $string_main_33, %rdi  # line 138, col 9
movq $0, %rax  # line 138, col 9
call printf  # line 138, col 9
popq %r11  # line 138, col 9
popq %r10  # line 138, col 9
movq %rax, %@temp_77  # line 138, col 9
pushq %r10  # line 139, col 9
pushq %r11  # line 139, col 9
movq %@local_a_55, %rsi  # line 139, col 9
movq $string_main_34, %rdi  # line 139, col 9
movq $0, %rax  # line 139, col 9
call printf  # line 139, col 9
popq %r11  # line 139, col 9
popq %r10  # line 139, col 9
movq %rax, %@temp_78  # line 139, col 9
pushq %r10  # line 140, col 9
pushq %r11  # line 140, col 9
movq $string_main_35, %rdi  # line 140, col 9
movq $0, %rax  # line 140, col 9
call printf  # line 140, col 9
popq %r11  # line 140, col 9
popq %r10  # line 140, col 9
movq %rax, %@temp_79  # line 140, col 9
pushq %r10  # line 141, col 9
pushq %r11  # line 141, col 9
movq %@local_b_56, %rsi  # line 141, col 9
movq $string_main_36, %rdi  # line 141, col 9
movq $0, %rax  # line 141, col 9
call printf  # line 141, col 9
popq %r11  # line 141, col 9
popq %r10  # line 141, col 9
movq %rax, %@temp_80  # line 141, col 9
pushq %r10  # line 142, col 9
pushq %r11  # line 142, col 9
movq $string_main_37, %rdi  # line 142, col 9
movq $0, %rax  # line 142, col 9
call printf  # line 142, col 9
popq %r11  # line 142, col 9
popq %r10  # line 142, col 9
movq %rax, %@temp_81  # line 142, col 9
jmp L32  # line 119, col 5
L32:  # line 119, col 5
movq %@local_x_59, %@s_165790  # line 119, col 5
addq $1, %@s_165790  # line 119, col 5
movq %@s_165790, %@local_x_59  # line 119, col 5
jmp L30  # line 119, col 5
