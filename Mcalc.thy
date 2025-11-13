(*
  TODO:
    - Add rules to reason about preservation of types
*)

theory Mcalc
  imports Solidity WP
begin

section "Weakest precondition calculus"

text \<open>Some adaptations to the general wp calculus\<close>

declare(in Contract) inv_state_def[wpsimps]
declare icall_def[wpsimps]
declare ecall_def[wpsimps]

declare(in Contract) wp_assign_stack_kdvalue[wprules del]

declare(in Contract) wp_stackCheck[wprules del]
lemma (in Contract) wp_assign_stack_kdvalue_memory[wprules]:
  assumes "Stack s $$ i = Some (kdata.Memory p)"
      and "mvalue_update xs (p, mdata.Value v, state.Memory s) = None \<Longrightarrow> E Err s"
      and "\<And>y. Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
         mvalue_update xs (p, mdata.Value v, state.Memory s) = Some y \<Longrightarrow>
         P Empty (Memory_update (K y) s)"
    shows "wp (assign_stack i xs (rvalue.Value v)) P E s"
  apply wp+
  using assms(1)
  apply (simp add:stack_check_def)
  apply wp+
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  apply wp+
  using assms by simp+

lemma (in Contract) wp_assign_stack_memory[wprules]:
  assumes "Stack s $$ i = Some (kdata.Memory p)"
      and "\<And>a list.
       Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
       is = a # list \<Longrightarrow> state.Memory s $ l = None \<Longrightarrow> E Err s"
      and "\<And>a list aa.
       Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
       is = a # list \<Longrightarrow>
       mvalue_update (a # list) (p, aa, state.Memory s) = None \<Longrightarrow>
       state.Memory s $ l = Some aa \<Longrightarrow> E Err s"
      and "is = [] \<Longrightarrow> P Empty (stack_update i (kdata.Memory l) s)"
      and "\<And>a list y aa.
       Stack s $$ i = Some (kdata.Memory p) \<Longrightarrow>
       is = a # list \<Longrightarrow>
       mvalue_update (a # list) (p, aa, state.Memory s) = Some y \<Longrightarrow>
       state.Memory s $ l = Some aa \<Longrightarrow> P Empty (Memory_update (K y) s)" 
  shows "wp (assign_stack i is (rvalue.Memory l)) P E s"
  apply wp+
  using assms(1)
  apply (simp add:stack_check_def)
  apply wp+
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  apply (cases "is")
  apply wp+
  using assms apply simp
  apply wp+
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  apply wp+
  apply (cases " state.Memory s $ l")
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  using assms apply simp
  apply (cases "state.Memory s $ l")
  apply (auto simp add:memory_update_monad_def my_update_monad_def)
  using assms by simp+

declare(in Contract) wp_stackCheck[wprules]

lemma is_Array_minit:
  assumes "Memory.minit cd ba = (l, baa)"
      and "mlookup baa y l = Some a"
      and "baa $ a = Some b"
      and "\<exists>as. alookup y cd = Some (adata.Array as)"
    shows "mdata.is_Array b"
  using assms
proof -
  have *: "a_data.copy_safe {||} baa l = Some cd"
    using minit_copy[OF assms(1)] by (simp add: a_data.copy_def prefix_id)
  then obtain as where "a_data.copy_safe {||} baa a = Some (adata.Array as)" using copy_memory_alookup_obtains[OF * assms(2)]
    using assms(4) by fastforce
  then show ?thesis using assms(3)
    by (metis assms(2) adata.distinct(1) acopy_safe_def data.mlookup_copy_memory_safe mdata.collapse(1) mdata.exhaust_disc)
qed

declare(in Contract) assign_stack.simps [simp del]

section "Memory Calculus"

definition pred_memory where
  "pred_memory i P r s =
    (case (Stack s) $$ i of
      Some (kdata.Memory l) \<Rightarrow> pred_some P (acopy (State.Memory s) l)
    | _ \<Rightarrow> False)"

text \<open>Needs to be used manually\<close>
lemma pred_some_copy_memory:
  assumes "acopy m l = Some cd"
      and "P cd"
    shows "pred_some P (acopy m l)"
  using assms unfolding pred_some_def by auto

text \<open>This destruction rule needs to be instantiated manually\<close>

lemma aliasing:
  assumes "mvalue_update xs (l1, v, m) = Some m'"
      and "xs = xs1@ys"
      and "ys \<noteq> []"
      and "mlookup m xs1 l1 = Some l1'"
      and "m $ l1' = Some l1''"
      and "mlookup m xs2 l2 \<bind> ($) m = Some l1''"
    shows "mvalue_update (xs2 @ ys) (l2, v, m) = Some m'"
  using mlookup_append_same[OF assms(3,4,5,6)]
  by (metis assms(1,2) mvalue_update.simps)

lemma aliasing2:
  assumes "mvalue_update xs (l1, v, m) = Some m'"
      and "xs = xs1@ys"
      and "ys \<noteq> []"
      and "mlookup m xs2 l2 = Some l1'"
      and "m $ l1' = Some l1''"
      and "mlookup m xs1 l1 \<bind> ($) m = Some l1''"
    shows "mvalue_update (xs2 @ ys) (l2, v, m) = Some m'"
  using mlookup_append_same[OF assms(3,4,5,6)]
  by (metis assms(1,2) mvalue_update.simps)

subsection \<open>Safe List Lookup\<close>

lemma nth_some:
  assumes "mvalue_update xs (l0, v, m0) = Some m1"
      and "m0 $ l2 = Some aa"
      and "the (mlookup m0 xs l0) \<noteq> l2"
    shows "m1 $ l2 = Some aa"
proof -
  obtain l
    where 0: "mlookup m0 xs l0 = Some l"
    and m'_def: "m1 = m0[l:=v]"
    using mvalue_update_obtain[OF assms(1)] by auto
  then have "m0 $ l2 = m1 $ l2" using assms(3)
    by (metis length_list_update nth_list_update_neq nth_safe_def option.sel)
  then show ?thesis using assms(2) by argo
qed

subsection \<open>Memory Lookup\<close>

lemma mlookup_mupdate:
  assumes "mvalue_update xs (l0, v0, m0) = Some m1"
      and "mlookup m0 ys l1 = Some l1'"
      and "locations m0 ys l1 = Some (the (locations m0 ys l1))"
      and "the (mlookup m0 xs l0) |\<notin>| the (locations m0 ys l1)"
    shows "mlookup m1 ys l1 = Some l1'"
proof -
  have m1_def: "m1 = m0[(the (mlookup m0 xs l0)) := v0]" using mvalue_update_obtain[OF assms(1)] by fastforce
  then have "mlookup m1 ys l1 = mlookup m0 ys l1" using mlookup_update_val[OF assms(2) assms(3) assms(4)]
    by (simp add: assms(2))
  then show ?thesis using assms(2) by simp
qed

lemma mlookup_some_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "\<not>Option.is_none (alookup xs cd)"
    shows "mlookup m1 xs l0 = Some (the (mlookup m1 xs l0))"
  using assms
  by (metis is_none_code(1) mlookup_some option.distinct(1) option.exhaust_sel)

lemma mlookup_some_minit2:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "mlookup m0 xs l1 = Some (the (mlookup m0 xs l1))"
    shows "mlookup m1 xs l1 = Some (the (mlookup m1 xs l1))"
  using assms
  by (metis minit_sprefix mlookup_prefix_mlookup snd_conv sprefix_prefix)

lemma mlookup_nth_mupdate:
  assumes "mvalue_update xs (l1, v, m0) = Some m1"
      and "the (mlookup m0 xs l1) |\<notin>| the (locations m0 xs l1)"
    shows "mlookup m1 xs l1 \<bind> ($) m1 = Some v"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 xs l1 = Some l"
      and "l < length m0"
      and "m1 = m0[l:=v]"
    using mvalue_update_obtain by metis
  moreover from l_def obtain L where "locations m0 xs l1 = Some L"
    using mlookup_locations_some by blast
  ultimately show ?thesis
    by (metis assms(2) bind.bind_lunit length_list_update mlookup_update_val nth_list_update_eq nth_safe_some
        option.sel)
qed

lemma mlookup_neq_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "mlookup m1 ys l0 = Some l2"
      and "mlookup m0 xs l1 = Some (the (mlookup m0 xs l1))"
      and "the (mlookup m0 xs l1) \<in> loc m0"
    shows "the (mlookup m1 xs l1) \<noteq> l2"
proof -
  from assms(1) have "sprefix m0 m1" using minit_sprefix by (metis snd_conv)
  then have "prefix m0 m1" using sprefix_prefix by auto
  moreover from minit_alocs[OF assms(1)] obtain L
    where "alocs_safe {||} m1 l0 = Some L"
      and *: "fset L \<inter> loc m0 = {}"
      unfolding s_disj_fs_def pred_some_def Utils.s_union_fs_def pred_some_def unfolding alocs_safe_def alocs_def data.locs_def by blast
  then have "l2 |\<in>| L" using a_data.locs_safe_mlookup assms(2) by blast
  with * have "l2 \<notin> loc m0" by blast
  ultimately show ?thesis using assms(3,4)
    by (metis \<open>prefix m0 m1\<close> mlookup_prefix_mlookup)
qed

lemma mlookup_neq_minit22:
  assumes "Memory.minit cd m0 = (l, m1)"
      and "mlookup m1 ys l0 = Some l2"
      and "mlookup m0 xs l1 = Some (the (mlookup m0 xs l1))"
      and "mlookup m0 ys l0 = Some (the (mlookup m0 ys l0))"
      and "mlookup m0 ys l0 = Some l2 \<Longrightarrow> the (mlookup m0 xs l1) \<noteq> l2"
    shows "the (mlookup m1 xs l1) \<noteq> l2"
proof -
  from assms(1) have *: "prefix m0 m1"
    by (metis minit_sprefix snd_conv sprefix_prefix)
  with assms(2,4) have "mlookup m0 ys l0 = Some l2"
    by (metis mlookup_prefix_mlookup)
  with assms(5) have "the (mlookup m0 xs l1) \<noteq> l2" by blast
  with * show ?thesis
    by (metis assms(3) mlookup_prefix_mlookup)
qed

lemma mlookup_neq_mupdate2:
  assumes "mvalue_update xs (l0, v, m0) = Some m1"
      and "mlookup m1 zs laa = Some x"
      and "mlookup m0 zs laa = Some (the (mlookup m0 zs laa))"
      and "mlookup m0 ys l1 = Some (the (mlookup m0 ys l1))"
      and "the (mlookup m0 xs l0) |\<notin>| the (locations m0 zs laa)"
      and "the (mlookup m0 xs l0) |\<notin>| the (locations m0 ys l1)"
      and "mlookup m0 zs laa = Some x \<Longrightarrow> the (mlookup m0 ys l1) \<noteq> x"
    shows "the (mlookup m1 ys l1) \<noteq> x"
proof -
  obtain l
    where 0: "mlookup m0 xs l0 = Some l"
    and m'_def: "m1 = m0[l:=v]"
    using mvalue_update_obtain[OF assms(1)] by auto
  moreover from assms(2,3,5,7) have "the (mlookup m0 ys l1) \<noteq> x"
    by (metis "0" m'_def mlookup_locations_some mlookup_update_val option.sel)
  ultimately show ?thesis using assms(4,6)
    by (metis mlookup_locations_some mlookup_update_val option.sel)
qed

lemma mlookup_neq_mupdate:
  assumes "mvalue_update ys (l1, v, m0) = Some m1"
      and "mlookup m0 xs l0 = Some l0'"
      and "m0 $ l0' = Some v"
      and "mlookup m1 as l2 = Some yg"
      and "zs \<noteq> []"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 ys l1)"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 (xs @ zs) l0)"
      and "mlookup m0 as l2 = Some (the (mlookup m0 as l2))"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 as l2)"
      and "mlookup m0 (xs @ zs) l0 = Some (the (mlookup m0 (xs @ zs) l0))"
      and "mlookup m0 as l2 = Some yg \<Longrightarrow> the (mlookup m0 (xs @ zs) l0) \<noteq> yg"
    shows "the (mlookup m1 (ys @ zs) l1) \<noteq> yg"
proof -
  from assms(10) obtain L where "locations m0 (xs @ zs) l0 = Some L"
    using mlookup_locations_some by blast
  then obtain L' L''
    where L'_def: "locations m0 xs l0 = Some L'"
      and L''_def: "locations m0 zs l0' = Some L''"
      and 1: "locations m0 (xs @ zs) l0 = Some (L' |\<union>| L'')"
    using locations_app_mlookup_exists[OF _ assms(2)] by force

  obtain l
    where 0: "mlookup m0 ys l1 = Some l"
    and m'_def: "m1 = m0[l:=v]"
    and "l < length m0"
  using mvalue_update_obtain[OF assms(1)] by auto
  then have *: "m1 $ l = m0 $ l0'" unfolding nth_safe_def
    by (metis assms(3) length_list_update nth_list_update_eq nth_safe_def)
  moreover
  from L'_def L''_def 1 have "\<forall>l|\<in>|the (locations m0 zs l0'). m0 $ l = m1 $ l"
   using assms(1,7) 0 m'_def
   by (metis funionI2 length_list_update nth_safe_def nth_some option.sel)
  moreover from assms(6) have "\<forall>l|\<in>|the (locations m0 ys l1). m0 $ l = m1 $ l"
    using m'_def `l < length m0` unfolding nth_safe_def apply (auto)
    by (metis "0" nth_list_update_neq option.sel)
  moreover obtain ll where "mlookup m0 zs l0' = Some ll"
    by (metis append_self_conv2 assms(2,10) mlookup.simps(1) mlookup_append) 
  moreover from assms(1,4,8,9) have "mlookup m0 as l2 = Some yg"
    by (metis mlookup_neq_mupdate2 option.sel)
  then have "ll \<noteq> yg"
    by (metis assms(2,11) bind_eq_Some_conv calculation(4) mlookup_append option.sel)
  ultimately show ?thesis using mlookup_mlookup_mlookup[OF 0 * assms(5)] by fastforce
qed

lemma mlookup_loc_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "\<not> Option.is_none (alookup xs cd)"
    shows "the (mlookup m1 xs l0) \<in> loc m1"
proof -
  from Memory.minit_loc[OF assms(1)] obtain L
    where "alocs m1 l0 = Some L"
      and "loc m1 = loc m0 \<union> fset L"
    unfolding Utils.s_union_fs_def pred_some_def alocs_safe_def alocs_def data.locs_def
    by blast
  moreover from mlookup_some[OF assms(1)] assms(2)
  obtain y where "mlookup m1 xs l0 = Some y"
    by force
  ultimately show ?thesis
    by (metis UnCI option.sel a_data.locs_mlookup)
qed

lemma mlookup_loc_minit2:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "mlookup m0 xs l1 = Some (the (mlookup m0 xs l1))"
      and "the (mlookup m0 xs l1) \<in> loc m0"
    shows "the (mlookup m1 xs l1) \<in> loc m1"
proof -
  from assms(1) have *: "prefix m0 m1"
    by (metis minit_sprefix snd_conv sprefix_prefix)
  with assms(2,3) have "the (mlookup m1 xs l1) \<in> loc m0"
    using mlookup_prefix_mlookup by fastforce
  then show ?thesis using * unfolding loc_def
    by (metis mem_Collect_eq nth_safe_length nth_safe_prefix nth_safe_some)
qed

lemma mlookup_nin_loc_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "mlookup m1 xs l0 = Some (the (mlookup m1 xs l0))"
    shows "the (mlookup m1 xs l0) \<notin> loc m0"
  using assms
  by (metis mlookup.simps(1) mlookup_neq_minit)

subsection \<open>Locations\<close>

lemma locations_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "\<not>Option.is_none (alookup xs cd)"
    shows "locations m1 xs l0 = Some (the (locations m1 xs l0))"
  using assms
  by (metis is_none_code(2) is_none_mlookup_locations is_none_simps(1) mlookup_some_minit option.collapse)

lemma locations_minit1:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "locations m0 ys l1 = Some (the (locations m0 ys l1))"
    shows "locations m1 ys l1 = Some (the (locations m1 ys l1))"
proof -
  from assms(1) have *: "prefix m0 m1"
    by (metis minit_sprefix snd_conv sprefix_prefix)
  then have "locations m1 ys l1 = Some (the (locations m0 ys l1))"
    using locations_prefix_locations[OF _ *] assms(2) by simp
  then show ?thesis by simp
qed

lemma locations_mupdate:
  assumes "mvalue_update xs (l0, v, m0) = Some m1"
      and "the (mlookup m0 xs l0) |\<notin>| (the (locations m0 ys l1))"
      and "locations m0 ys l1 = Some (the (locations m0 ys l1))"
    shows "locations m1 ys l1 = Some (the (locations m1 ys l1))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 xs l0 = Some l"
      and "l < length m0"
      and "m1 = m0[l:=v]"
    using mvalue_update_obtain by metis
  then have "locations m1 ys l1 = Some (the (locations m0 ys l1))"
    by (smt (verit) assms(1,2,3) length_list_update locations_same nth_safe_def nth_some)
  then show ?thesis by auto
qed

subsection \<open>Memory Lookup and Locations\<close>

lemma mlookup_locations_minit_1:
  assumes "Memory.minit cd m0 = (l, m1)"
      and "\<not> Option.is_none (alookup xs cd)"
    shows "the (mlookup m1 xs l) |\<notin>| the (locations m1 xs l)" 
  using assms locations_minit minit_mlookup_locations mlookup_some_minit by blast

lemma mlookup_locations_minit_2:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "\<not> Option.is_none (alookup ys cd)"
      and "mlookup m0 xs l1 = Some (the (mlookup m0 xs l1))"
      and "the (mlookup m0 xs l1) \<in> loc m0"
    shows "the (mlookup m1 xs l1) |\<notin>| the (locations m1 ys l0)"
proof -
  have *: "prefix m0 m1" using minit_sprefix[of m0 cd] assms(1) sprefix_prefix by simp

  from minit_locations_some[OF assms(1), of ys]
  obtain L' where L'_def: "locations m1 ys l0 = Some L'" using assms(2) by fastforce
  moreover obtain L where L_def: "alocs m1 l0 = Some L" and **: "fset L \<inter> loc m0 = {}"
    using minit_alocs[OF assms(1)] unfolding pred_some_def s_disj_fs_def by auto
  ultimately have "L' |\<subseteq>| L" using a_data.locs_locations by blast
  moreover from assms(3,4) obtain l where "mlookup m0 xs l1 = Some l" and ***: "l \<in> loc m0" by blast
  then have "mlookup m1 xs l1 = Some l" using mlookup_prefix_mlookup * by blast
  ultimately show ?thesis using ** *** L'_def unfolding pred_some_def by auto
qed

lemma mlookup_locations_minit_21:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "\<not> Option.is_none (alookup xs cd)"
      and "locations m0 ys l1 = Some (the (locations m0 ys l1))"
    shows "the (mlookup m1 xs l0) |\<notin>| the (locations m1 ys l1)"
proof -
  have *: "prefix m0 m1" using minit_sprefix[of m0 cd] assms(1) sprefix_prefix by simp

  from mlookup_some[OF assms(1), of xs]
  obtain l where l_def: "mlookup m1 xs l0 = Some l" using assms(2) by fastforce
  moreover have "l \<notin> loc m0"
    by (metis assms(1) l_def mlookup_nin_loc_minit option.sel)
  moreover have "fset (the (locations m0 ys l1)) \<subseteq> loc m0" using locations_subs_loc[OF assms(3)] by blast
  ultimately show ?thesis using assms
    by (metis "*" locations_prefix_locations option.sel subsetD)
qed

lemma mlookup_locations_minit_3:
  assumes "Memory.minit cd m0 = (l, m1)"
    and "mlookup m0 xs x1 = Some (the (mlookup m0 xs x1))"
    and "locations m0 ys x2 = Some (the (locations m0 ys x2))"
    and "the (mlookup m0 xs x1) |\<notin>| the (locations m0 ys x2)"
  shows "the (mlookup m1 xs x1) |\<notin>| the (locations m1 ys x2)"
proof -
  from assms(1) have "sprefix m0 m1" using minit_sprefix
    by (metis snd_conv)
  then have "prefix m0 m1" using sprefix_prefix by auto
  then have "mlookup m1 xs x1 = Some (the (mlookup m0 xs x1))" using mlookup_prefix_mlookup[OF assms(2)] by simp
  moreover have "locations m1 ys x2 = Some (the (locations m0 ys x2))"
    using locations_prefix_locations[OF assms(3) `prefix m0 m1`] by blast
  ultimately show ?thesis using assms(4) by simp
qed

lemma mlookup_locations_mupdate_1:
  assumes "mvalue_update xs (l0, v, m0) = Some m1"
      and "mlookup m0 ys l1 = Some l0'"
      and "m0 $ l0' = Some v"
      and "zs = z # zs'"
      and "the (mlookup m0 xs l0) |\<notin>| the (locations m0 xs l0)"
      and "locations m0 (xs @ zs) l0 = Some (the (locations m0 (xs @ zs) l0))"
      and "the (mlookup m0 xs l0) |\<notin>| the (locations m0 (ys @ zs) l1)"
      and "the (mlookup m0 (ys @ zs) l1) |\<notin>| the (locations m0 (xs @ zs) l0)"
      and "mlookup m0 (ys @ zs) l1 = Some (the (mlookup m0 (ys @ zs) l1))"
      and "the (mlookup m0 (ys @ zs) l1) |\<notin>| the (locations m0 (ys @ zs) l1)"
    shows "the (mlookup m1 (xs @ zs) l0) |\<notin>| the (locations m1 (xs @ zs) l0)"
proof -
  from assms(9) have a0: "locations m0 (ys @ zs) l1 = Some (the (locations m0 (ys @ zs) l1))"
    by (simp add: mlookup_locations_some)

  obtain L L'
    where L_def: "locations m0 ys l1 = Some L"
      and L'_def: "locations m0 zs l0' = Some L'"
      and 1: "locations m0 (ys @ zs) l1 = Some (L |\<union>| L')"
    using locations_app_mlookup_exists[OF a0 assms(2)] by (metis a0)
  from L'_def obtain l''
    where l''_def: "mlookup m0 [z] l0' = Some l''"
    using assms(4)
    apply (auto simp add:locations.simps mlookup.simps case_memory_def split:option.split_asm mdata.split_asm)
    apply (case_tac "vtype_class.to_nat z", auto)
    by (case_tac "x2a$a", auto)
  then obtain L''
    where L''_def: "locations m0 zs' (the (mlookup m0 [z] l0')) = Some L''"
      and 2: "L'' |\<subseteq>| L'"
    using locations_cons_mlookup_exists L'_def assms(4) by (metis option.sel)

  obtain l
    where 3: "mlookup m0 xs l0 = Some l"
    and m'_def: "m1 = m0[l:=v]"
    and 4: "length m0 > l"
  using mvalue_update_obtain[OF assms(1)] by auto
  then have "m0 $ l0' = m1 $ l" unfolding nth_safe_def
    by (metis assms(3) length_list_update nth_list_update_eq nth_safe_def)
  moreover have *: "locations m0 xs l0 = Some (the (locations m0 xs l0))"
    by (simp add: "3" mlookup_locations_some)
  moreover have **: "\<forall>l|\<in>|the (locations m0 xs l0). m0 $ l = m1 $ l"
    using assms(5) 3 m'_def unfolding nth_safe_def apply auto
    by (metis nth_list_update_neq)
  moreover
    have ***: "locations m0 zs' (the (mlookup m0 [z] l0'))
      = Some (the (locations m0 zs' (the (mlookup m0 [z] l0'))))"
      using L''_def by simp
  moreover have "\<forall>l|\<in>|the (locations m0 zs' (the (mlookup m0 [z] l0'))). m0 $ l = m1 $ l"
  proof
    fix l' assume "l' |\<in>| the (locations m0 zs' (the (mlookup m0 [z] l0')))"
    then have "l' |\<in>| the (locations m0 (ys @ zs) l1)"
      using L''_def 2 1 by auto
    then show "m0 $ l' = m1 $ l'"
      using assms(7) m'_def 3 unfolding nth_safe_def apply auto
      by (metis nth_list_update_neq)
  qed
  moreover have "mlookup m0 [z] l0' = Some (the (mlookup m0 [z] l0'))"
    using l''_def by auto
  ultimately have
    "locations m1 (xs @ zs) l0
      = Some (finsert l (the (locations m0 xs l0))
      |\<union>| the (locations m0 zs' (the (mlookup m0 [z] l0'))))" 
    using locations_union_mlookup_nth[OF assms(4) 3 , of _ _ _  "the (locations m0 xs l0)"]
    by simp
  moreover have "the (mlookup m1 (xs @ zs) l0) = the (mlookup m0 (ys @ zs) l1)"
  proof -
    from L'_def L''_def 1 have "\<forall>l|\<in>|the (locations m0 zs l0'). m0 $ l = m1 $ l"
      using assms(7) 3 m'_def
      by (metis funionI2 length_list_update nth_list_update_neq nth_safe_def option.sel)
    moreover from assms(2,9)
      obtain ll where "mlookup m0 zs l0' = Some ll" by (simp add: mlookup_append)
    ultimately show ?thesis using mlookup_mlookup_mlookup[OF 3, of m1 l0' zs ll] \<open>m0 $ l0' = m1 $ l\<close> ** assms(4)
      by (simp add: assms(2) mlookup_append)
  qed
  moreover from assms(4,6)
    have "(finsert l (the (locations m0 xs l0)) |\<subseteq>| the (locations m0 (xs @ zs) l0))"
    by (metis "3" * finsert_fsubset list.distinct(1) locations_append_subset mlookup_in_locations
        option.inject)
  moreover from assms(10)
    have "the (locations m0 zs' (the (mlookup m0 [z] l0'))) |\<subseteq>| the (locations m0 (ys @ zs) l1)"
      using L''_def 1 2 by auto
  ultimately show ?thesis using assms(8,10) by auto
qed

lemma mlookup_locations_mupdate_2:
  assumes "mvalue_update ys (l1, v, m0) = Some m1"
      and "mlookup m0 xs l0 = Some l0'"
      and "m0 $ l0' = Some v"
      and "zs \<noteq> []"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 ys l1)"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 xs l0)"
      and "locations m0 as l2 = Some (the (locations m0 as l2))"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 as l2)"
      and "mlookup m0 (xs @ zs) l0 = Some (the (mlookup m0 (xs @ zs) l0))"
      and "the (mlookup m0 ys l1) |\<notin>| the (locations m0 (xs @ zs) l0)"
      and "the (mlookup m0 (xs @ zs) l0) |\<notin>| the (locations m0 as l2)"
    shows "the (mlookup m1 (ys @ zs) l1) |\<notin>| the (locations m1 as l2)"
proof -
  obtain l
    where 0: "mlookup m0 ys l1 = Some l"
    and m'_def: "m1 = m0[l:=v]"
    and "l < length m0"
  using mvalue_update_obtain[OF assms(1)] by auto
  then have *:"m1 $ l = Some v" unfolding nth_safe_def by simp
  moreover have "l |\<notin>| the (locations m0 ys l1)" using assms(5) 0 by simp
  then have **: "mlookup m1 ys l1 = Some l" using m'_def
    by (metis "0" assms(1) mlookup_locations_some mlookup_mupdate option.sel)
  moreover have "mlookup m1 xs l0 = Some (the (mlookup m0 xs l0))" using assms
    by (simp add: mlookup_locations_some mlookup_mupdate)
  then have ***: "mlookup m1 xs l0 \<bind> ($) m1 = Some v" using assms(1,2)
    by (metis "*" "0" assms(3) bind.bind_lunit nth_some option.sel)
  ultimately have "mlookup m1 (ys @ zs) l1 = mlookup m1 (xs @ zs) l0" using mlookup_append_same[OF assms(4) ** * ***] by simp
  moreover from assms(9,10) 0 m'_def have "mlookup m1 (xs @ zs) l0 = mlookup m0 (xs @ zs) l0"
    by (metis mlookup_locations_some mlookup_update_val option.sel)
  moreover from assms(7,8) 0 m'_def have "\<forall>l|\<in>|the (locations m0 as l2). m1 $ l = m0 $ l" unfolding nth_safe_def apply (auto)
    by (metis nth_list_update_neq)
  with assms(7,8) 0 m'_def have "the (locations m1 as l2) = the (locations m0 as l2)"
    by (metis locations_same)
  ultimately show ?thesis by (simp add: assms(11))
qed

subsection \<open>Memory Locations\<close>

lemma locs_locs_minit_1:
  assumes "Memory.minit cd m0 = (l0, m1)"
    shows "alocs m1 l0 = Some (the (alocs m1 l0))"
  using Memory.minit_loc[OF assms(1)] unfolding s_union_fs_def pred_some_def by auto

lemma locs_locs_minit_2:
  assumes "Memory.minit cd m0 = (l1, m1)"
    and "alocs m0 l = Some (the (alocs m0 l))"
  shows "alocs m1 l = Some (the (alocs m1 l))"
proof -
  from assms(1) have "prefix m0 m1"
    by (metis minit_sprefix snd_eqD sprefix_prefix)
  then show ?thesis
    by (metis assms(2) a_data.locs_prefix)
qed

lemma locs_locs_disj_minit:
  assumes "Memory.minit cd m0 = (l1, m1)"
    and "alocs m0 l0 = Some (the (alocs m0 l0))"
  shows "the (alocs m1 l0) |\<inter>| the (alocs m1 l1) = {||}"
proof -
  from assms(1) have "prefix m0 m1"
    by (metis minit_sprefix snd_eqD sprefix_prefix)
  moreover from assms(2) have "fset (the (alocs m0 l0)) \<subseteq> loc m0" using a_data.locs_subs2 by auto
  ultimately have "fset (the (alocs m1 l0)) \<subseteq> loc m0"
    by (metis assms(2) a_data.locs_prefix)
  then show ?thesis using minit_alocs[OF assms(1)] unfolding s_disj_fs_def pred_some_def
    by auto
qed

lemma locs_some_mupdate_value:
  assumes "mvalue_update is1 (l1, mdata.Value v, m0) = Some m1"
      and "alocs m0 l1 = Some (the (alocs m0 l1))"
    shows "alocs m1 l1 = Some (the (alocs m1 l1))"
  using assms
    a_data.mupdate_locs_subset[of m0 l1 m1 _ "v"]
    mvalue_update_obtain[OF assms(1)]
  apply (cases "mlookup m0 is1 l1")
  apply (auto simp add: mvalue_update.simps list_update_safe_def split:if_split_asm)
  by fastforce

lemma locs_some_mupdate_1:
  assumes "mvalue_update is1 (l1, v, m0) = Some m1"
      and "mlookup m0 is2 l2 = Some l2'"
      and "m0 $ l2' = Some v"
      and "acheck m0 (the (alocs m0 l1))"
      and "the (alocs m0 l1) |\<inter>| the (alocs m0 l2) = {||}"
      and "alocs m0 l2 = Some (the (alocs m0 l2))"
      and "alocs m0 l1 = Some (the (alocs m0 l1))"
    shows "alocs m1 l1 = Some (the (alocs m1 l1))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 is1 l1 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=v]" using mvalue_update_obtain by metis
  then have 0: "m1 $ l = m0 $ l2'" by (simp add: assms(3))
  moreover from assms(7) obtain L1 where L1_def: "alocs m0 l1 = Some L1" by simp
  moreover from assms(2,6) obtain L2 where L2_def: "alocs m0 l2' = Some L2" and *: "L2 |\<subseteq>| the (alocs m0 l2)"
    by (metis a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover from L1_def obtain L1' where "alocs m0 l = Some L1'" using l_def
    by (metis a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have "\<forall>l|\<in>|L1 |-| L1'. m1 $ l = m0 $ l"
  proof
    fix l' assume "l' |\<in>|L1 |-| L1'"
    moreover have "l |\<notin>| L1 |-| L1'"
      by (meson \<open>alocs m0 l = Some L1'\<close> fminusD2 a_data.locs_subs)
    ultimately have "l \<noteq> l'" by blast
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by simp
  qed
  moreover have "\<forall>l|\<in>|L2. m1 $ l = m0 $ l"
  proof
    fix l' assume "l'|\<in>|L2"
    moreover have "l |\<in>|L1"
      using L1_def l_def a_data.locs_mlookup by blast
    ultimately have "l \<noteq> l'" using assms(5) L1_def L2_def * by auto
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover from assms(4) have "acheck m0 L1" using L1_def by auto
  moreover have "the (locations m0 is1 l1) |\<inter>| L2 = {||}"
  proof -
    from l_def obtain LL where "locations m0 is1 l1 = Some LL"
      using mlookup_locations_some by blast
    then have "LL |\<subseteq>| L1" using L1_def using a_data.locs_locations by blast
    then show ?thesis using assms(5) *
      using L1_def \<open>locations m0 is1 l1 = Some LL\<close> by auto
  qed
  moreover have "l |\<notin>| L2"
  proof -
    have "l |\<in>| L1"
      using L1_def l_def a_data.locs_mlookup by blast
    then show ?thesis using assms(5) * L2_def L1_def by auto
  qed
  ultimately show ?thesis using locs_update_some[OF l_def 0, of L1 L1' L2] by simp
qed

lemma locs_some_mupdate_2:
  assumes "mvalue_update xs (l0, v, m0) = Some m1"
    and "the (mlookup m0 xs l0) |\<notin>| the (alocs m0 l)"
    and "alocs m0 l = Some (the (alocs m0 l))"
  shows "alocs m1 l = Some (the (alocs m1 l))"
proof -
  obtain l'
    where 0: "mlookup m0 xs l0 = Some l'"
    and m'_def: "m1 = m0[l':=v]"
  using mvalue_update_obtain[OF assms(1)] by auto
  moreover from assms(2) have "\<forall>l''|\<in>|the (alocs m0 l). m1 $ l'' = m0 $ l''"
    using 0 m'_def unfolding nth_safe_def apply (simp split:if_split_asm)
    by (metis nth_list_update_neq)
  ultimately show ?thesis using a_data.locs_same[of m0 l] by (metis assms(3))
qed

lemma locs_disj_minit:
assumes "Memory.minit z m0 = (laa, m1)"
    and "alocs m0 x1 = Some (the (alocs m0 x1))"
    and "alocs m0 la = Some (the (alocs m0 la))"
    and "the (alocs m0 x1) |\<inter>| the (alocs m0 la) = {||}"
  shows "the (alocs m1 x1) |\<inter>| the (alocs m1 la) = {||}"
proof -
  from assms(1) have "prefix m0 m1"
    by (metis minit_sprefix snd_conv sprefix_prefix)
  moreover from assms(2) obtain L where "alocs m0 x1 = Some L" by blast
  ultimately have "alocs m1 x1 = Some L" using a_data.locs_prefix by auto
  moreover from assms(3) obtain L' where L'_def: "alocs m0 la = Some L'" by blast
  moreover have "alocs m1 la = Some L'" using L'_def `prefix m0 m1` a_data.locs_prefix by auto
  ultimately show ?thesis using assms(4)
    by (simp add: \<open>alocs m0 x1 = Some L\<close>)
qed

lemma locs_disj_mupdate:
  assumes "mvalue_update is1 (l1, v, m0) = Some m1"
      and "mlookup m0 is2 l2 = Some l2'"
      and "m0 $ l2' = Some v"
      and "alocs m0 l1 = Some (the (alocs m0 l1))"
      and "alocs m0 l2 = Some (the (alocs m0 l2))"
      and "alocs m0 la = Some (the (alocs m0 la))"
      and "the (alocs m0 l1) |\<inter>| the (alocs m0 l2) = {||}"
      and "the (mlookup m0 is1 l1) |\<notin>| the (alocs m0 la)"
      and "acheck m0 (the (alocs m0 l1))"
      and "the (alocs m0 l1) |\<inter>| the (alocs m0 la) = {||}"
      and "the (alocs m0 l2) |\<inter>| the (alocs m0 la) = {||}"
    shows "the (alocs m1 l1) |\<inter>| the (alocs m1 la) = {||}"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 is1 l1 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=v]" using mvalue_update_obtain by metis
  then have 0: "m1 $ l = m0 $ l2'" by (simp add: assms(3))
  moreover obtain L0 where "alocs m1 l1 = Some L0" using locs_some_mupdate_1[OF assms(1,2,3,9,7,5,4)] by simp
  moreover from assms(4) obtain L1 where L1_def: "alocs m0 l1 = Some L1" by simp
  moreover from assms(5) obtain L2 where L2_def: "alocs m0 l2' = Some L2" and ***: "L2 |\<subseteq>| the (alocs m0 l2)"
    by (metis assms(2) a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have "alocs m0 l = Some (the (alocs m0 l))"
    by (metis L1_def l_def option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have "\<forall>l|\<in>|L1 |-| the (alocs m0 l). m1 $ l = m0 $ l" using ** unfolding nth_safe_def apply (simp split:if_split_asm)
    by (metis Diff_iff calculation(6) nth_list_update_neq a_data.locs_subs)
  moreover have "\<forall>l|\<in>|the (alocs m0 l2). m1 $ l = m0 $ l"
  proof
    fix l' assume "l'|\<in>|the (alocs m0 l2)"
    moreover from l_def have "l|\<in>|the (alocs m0 l1)" using a_data.locs_mlookup[OF L1_def] L1_def by simp
    ultimately have "l' \<noteq> l" using assms(7) L1_def L2_def by auto
    then show "m1 $ l' = m0 $ l'" using ** unfolding nth_safe_def by simp
  qed
  then have "\<forall>l|\<in>|L2. m1 $ l = m0 $ l" using *** by blast
  moreover from assms(9) have "acheck m0 L1" using L1_def by simp
  ultimately have "L0 |\<subseteq>| L1 |\<union>| L2" using locs_update_subs[OF l_def 0, of L1 "the (alocs m0 l)" L2 L0] by blast
  moreover have "L2 |\<subseteq>| the (alocs m0 l2)"
    by (metis \<open>alocs m0 l2' = Some L2\<close> assms(2,5) a_data.locs_def a_data.mlookup_locs_subs)
  moreover have "the (alocs m0 la) = the (alocs m1 la)"
  proof -
    obtain L where L_def: "alocs m0 la = Some L" using assms(6) by simp
    moreover from assms(8) ** * have "\<forall>l |\<in>| L. m0$l = m1$l" unfolding nth_safe_def l_def apply (auto split:if_split_asm)
      by (metis calculation nth_list_update_neq option.sel)
    ultimately have "alocs m1 la = Some L"
      by (metis a_data.locs_same)
    then show ?thesis using L_def by simp
  qed
  ultimately show ?thesis using assms(10,11)
    using \<open>alocs m1 l1 = Some L0\<close> L1_def by auto
qed

subsection \<open>Memory Lookup and Memory Locations\<close>

lemma mlookup_locs_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "mlookup m0 is1 l1 = Some (the (mlookup m0 is1 l1))"
      and "the (mlookup m0 is1 l1) \<in> loc m0"
    shows "the (mlookup m1 is1 l1) |\<notin>| the (alocs m1 l0)"
proof -
  from assms(1) obtain L where L_def: "alocs m1 l0 = Some L"
    using locs_locs_minit_1 by blast
  then have "fset L \<inter> loc m0 = {}"
    by (metis Diff_disjoint Memory.minit_loc assms(1) inf_commute minit_alocs option.sel s_disj_union_fs)
  moreover from assms(1) have "prefix m0 m1"
    by (metis minit_sprefix snd_conv sprefix_prefix)
  with assms(2) have "the (mlookup m1 is1 l1) = the (mlookup m0 is1 l1)"
    by (metis mlookup_prefix_mlookup)
  ultimately show ?thesis using L_def assms by auto
qed

lemma mlookup_locs_minit2:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "mlookup m0 is1 l1 = Some (the (mlookup m0 is1 l1))"
      and "alocs m0 l = Some (the (alocs m0 l))"
      and "the (mlookup m0 is1 l1) |\<notin>| the (alocs m0 l)"
    shows "the (mlookup m1 is1 l1) |\<notin>| the (alocs m1 l)"
proof -
  from assms(1) have "prefix m0 m1"
    by (metis minit_sprefix snd_conv sprefix_prefix)
  then have "the (mlookup m0 is1 l1) = the (mlookup m1 is1 l1)"
    by (metis assms(2) mlookup_prefix_mlookup)
  moreover have "the (alocs m0 l) = the (alocs m1 l)"
    by (metis \<open>prefix m0 m1\<close> assms(3) a_data.locs_prefix)
  ultimately show ?thesis using assms(4) by simp
qed

subsection \<open>Copy Memory\<close>

lemma copy_minit:
  assumes "Memory.minit cd m0 = (l0, m1)"
      and "alocs m0 l1 = Some (the (alocs m0 l1))"
      and "acopy m0 l1 = Some cd'"
    shows "acopy m1 l1 = Some cd'"
  using assms
  by (metis minit_sprefix a_data.copy_memory_append snd_conv sprefix_prefix)

lemma copy_mupdate_value:
  assumes "mvalue_update xs (l0, mdata.Value v, m0) = Some m1"
      and "acheck m0 (the (alocs m0 l0))"
      and "acopy m0 l0 = Some cd0"
    shows "acopy m1 l0 = Some (the (aupdate xs (adata.Value v) cd0))" 
proof-
  from assms(1) obtain l
    where l_def: "mlookup m0 xs l0 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=mdata.Value v]" using mvalue_update_obtain by metis
  moreover have 1: "alocs_safe {||} m0 l0 = Some (the (alocs_safe {||} m0 l0))" using a_data.locs_copy_memory_some
    by (metis assms(3) option.sel a_data.copy_def)
  moreover have 2: "alocs_safe {||} m0 l = Some (the (alocs_safe {||} m0 l))"
    by (metis "1" l_def option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have 3: "\<forall>l'|\<in>|the (alocs_safe {||} m0 l0) |-| (the (alocs_safe {||} m0 l)). m1 $ l' = m0 $ l'"
  proof
    fix l' assume "l' |\<in>|the (alocs_safe {||} m0 l0) |-| (the (alocs_safe {||} m0 l))"
    moreover have "l |\<notin>| the (alocs_safe {||} m0 l0) |-| (the (alocs_safe {||} m0 l))"
      by (meson "2" fminusD2 a_data.locs_safe_subs)
    ultimately have "l \<noteq> l'" by blast
    then show " m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover from assms(2) have 4: "acopy_safe {||} m0 l0 = Some (the (acopy_safe {||} m0 l0))"
    by (metis assms(3) option.sel a_data.copy_def)
  moreover from assms obtain cd' where 6: "acopy_safe {||} m1 l0 = Some cd'"
    by (metis mvalue_update_obtain a_data.copy_memory_safe_update_value
        a_data.copy_def)
  ultimately show ?thesis using copy_memory_safe_lookup_update_value[OF l_def * ** 1 ]
    by (metis assms(2,3) option.distinct(1) option.exhaust_sel a_data.copy_def a_data.locs_def)
qed

lemma copy_mupdate:
  assumes "mvalue_update is1 (l1, v, m0) = Some m1"
      and "mlookup m0 is2 l2 = Some l2'"
      and "m0 $ l2' = Some v"
      and "acheck m0 (the (alocs m0 l1))"
      and "the (alocs m0 l1) |\<inter>| the (alocs m0 l2) = {||}"
      and "acopy m0 l1 = Some cd1"
      and "acopy m0 l2 = Some cd2"
    shows "acopy m1 l1 = Some (the (alookup is2 cd2 \<bind> (\<lambda>cd. aupdate is1 cd cd1)))"
proof-
  from assms(1) obtain l
    where l_def: "mlookup m0 is1 l1 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=v]" using mvalue_update_obtain by metis
  then have 0: "m1 $ l = m0 $ l2'" by (simp add: assms(3))
  moreover have 1: "alocs_safe {||} m0 l1 = Some (the (alocs_safe {||} m0 l1))" using a_data.locs_copy_memory_some
    by (metis assms(6) option.sel a_data.copy_def)
  moreover have 2: "alocs_safe {||} m0 l = Some (the (alocs_safe {||} m0 l))"
    by (metis "1" l_def option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have 3: "alocs_safe {||} m0 l2= Some (the (alocs_safe {||} m0 l2))"  using a_data.locs_copy_memory_some
    by (metis assms(7) option.sel a_data.copy_def)
  moreover have 4: "\<forall>l|\<in>|the (alocs_safe {||} m0 l1) |-| the (alocs_safe {||} m0 l). m1 $ l = m0 $ l"
  proof
    fix l' assume "l' |\<in>|the (alocs_safe {||} m0 l1) |-| (the (alocs_safe {||} m0 l))"
    moreover have "l |\<notin>| the (alocs_safe {||} m0 l1) |-| (the (alocs_safe {||} m0 l))"
      by (meson "2" fminusD2 a_data.locs_safe_subs)
    ultimately have "l \<noteq> l'" by blast
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover have 5: "\<forall>l|\<in>|the (alocs_safe {||} m0 l2'). m1 $ l = m0 $ l"
  proof
    fix l' assume "l'|\<in>| the (alocs_safe {||} m0 l2')"
    moreover have "l |\<in>| the (alocs_safe {||} m0 l1)"
      by (metis "1" data.locs_safe_mlookup l_def alocs_safe_def)
    moreover have 3: "alocs_safe {||} m0 l2'= Some (the (alocs_safe {||} m0 l2'))"  using a_data.locs_copy_memory_some
      by (metis assms(2,7) data.locs_safe_mlookup data.locs_safe_in_subs alocs_safe_def option.sel a_data.copy_def)
    ultimately have "l \<noteq> l'" using assms(5)
      by (smt (verit, ccfv_SIG) "3" assms(2,7) data.mlookup_locs_subs disjoint_iff_fnot_equal finsert_fsubset
          alocs_safe_def mk_disjoint_finsert option.sel a_data.copy_def a_data.locs_copy_memory_some
          a_data.locs_def)
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover have 6: "locations m0 is1 l1 = Some (the (locations m0 is1 l1))"
    by (simp add: l_def mlookup_locations_some)
  moreover have 7: "the (locations m0 is1 l1) |\<inter>| the (alocs_safe {||} m0 l2') = {||}"
  proof -
    have "the (locations m0 is1 l1) |\<subseteq>| the (alocs m0 l1)"
      by (metis "1" "6" a_data.locs_def a_data.locs_safe_locations)
    moreover have "the (alocs_safe {||} m0 l2') |\<subseteq>| the (alocs_safe {||} m0 l2)"
      by (metis "3" assms(2) option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
    ultimately show ?thesis using assms(5)
      by (metis (no_types, lifting) ext boolean_algebra_cancel.inf1 inf.order_iff inf_bot_right inf_commute
          a_data.locs_def)
  qed
  moreover have 8: "l |\<notin>| the (alocs_safe {||} m0 l2')" using assms(5)
  proof -
    have "l |\<in>| the (alocs_safe {||} m0 l1)"
      by (metis "1" data.locs_safe_mlookup l_def alocs_safe_def)
    moreover have 3: "alocs_safe {||} m0 l2'= Some (the (alocs_safe {||} m0 l2'))"  using a_data.locs_copy_memory_some
      by (metis assms(2,7) data.locs_safe_mlookup data.locs_safe_in_subs alocs_safe_def option.sel a_data.copy_def)
    ultimately show ?thesis using assms(5)
      by (smt (verit, ccfv_SIG) "3" assms(2,7) data.mlookup_locs_subs disjoint_iff_fnot_equal finsert_fsubset
          alocs_safe_def mk_disjoint_finsert option.sel a_data.copy_def a_data.locs_copy_memory_some
          a_data.locs_def)
  qed
  moreover have "alocs_safe {||} m0 l2'= Some (the (alocs_safe {||} m0 l2'))"  using a_data.locs_copy_memory_some
      by (metis assms(2,7) data.locs_safe_mlookup data.locs_safe_in_subs alocs_safe_def option.sel a_data.copy_def)
  ultimately obtain cd' where 9: "acopy_safe {||} m1 l1 = Some cd'"
    using a_data.update_some_obtains_copy[OF l_def 0 1 2 _ 4 5 _ _ _ 6 7 8] assms(4,6,7) 
    by (metis inf_bot_left a_data.copy_def a_data.locs_def
        a_data.locs_safe_copy_memory_safe)
  moreover have "\<forall>l|\<in>|the (alocs_safe {||} m0 l2). m1 $ l = m0 $ l"
  proof
    fix l' assume "l'|\<in>| the (alocs_safe {||} m0 l2)"
    moreover have "l |\<in>| the (alocs_safe {||} m0 l1)"
      by (metis "1" data.locs_safe_mlookup l_def alocs_safe_def)
    moreover have 3: "alocs_safe {||} m0 l2'= Some (the (alocs_safe {||} m0 l2'))"  using a_data.locs_copy_memory_some
      by (metis assms(2,7) data.locs_safe_mlookup data.locs_safe_in_subs alocs_safe_def option.sel a_data.copy_def)
    ultimately have "l \<noteq> l'" using assms(5) by (metis disjoint_iff_fnot_equal a_data.locs_def)
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover from assms(6) have "acopy_safe {||} m0 l1 = Some cd1"
    by (simp add: a_data.copy_def)
  moreover from assms(7) have "acopy_safe {||} m0 l2 = Some cd2"
    by (simp add: a_data.copy_def)
  moreover have "acheck m0 (the (alocs_safe {||} m0 l1))"
    by (metis assms(4) a_data.locs_def)
  ultimately show ?thesis using copy_memory_safe_lookup_update[OF l_def assms(2) 0 1 2 3 4 ]
    by (metis option.sel a_data.copy_def)
qed

lemma copy_memory_mupdate:
  assumes "mvalue_update is1 (l0, v, m0) = Some m1"
      and "the (mlookup m0 is1 l0) |\<notin>| the (alocs m0 l1)"
      and "acopy m0 l1 = Some cd0"
    shows "acopy m1 l1 = Some cd0"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 is1 l0 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=v]" using mvalue_update_obtain by metis
  moreover from assms(3) obtain L where L_def: "alocs m0 l1 = Some L"
    by (metis a_data.copy_def a_data.locs_copy_memory_some a_data.locs_def)
  moreover from assms(2) ** L_def l_def have "\<forall>l |\<in>| L. m1 $ l = m0 $ l" unfolding nth_safe_def
    apply (simp add: split:if_split_asm)
    by (metis nth_list_update_neq)
  ultimately show ?thesis using Memory.a_data.copy_memory_locs[OF assms(3)] by blast
qed

subsection \<open>Memory Check\<close>

lemma check_locs_minit_1:
  assumes "Memory.minit cd m = (x1, x2)"
    shows "acheck x2 (the (alocs x2 x1))"
proof -
  from assms(1) obtain L where "alocs x2 x1 = Some L" using locs_locs_minit_1 by blast
  then show ?thesis using minit_acheck[OF assms(1)]
    by (metis bot_fset.rep_eq empty_iff option.sel a_data.locs_def)
qed

lemma check_locs_minit_2:
  assumes "Memory.minit cd m0 = (l1, m1)"
      and "alocs m0 l0 = Some (the (alocs m0 l0))"
      and "acheck m0 (the (alocs m0 l0))"
    shows "acheck m1 (the (alocs m1 l0))"
proof -
  from assms(1) have "prefix m0 m1"
    by (metis minit_sprefix snd_eqD sprefix_prefix)
  moreover have "fset (the (alocs m0 l0)) \<subseteq> loc m0" using a_data.locs_subs2 assms(2) by blast
  ultimately have "acheck m1 (the (alocs m0 l0))" using a_data.check_prefix[OF _ _ assms(3)] assms(2)
    by (metis a_data.locs_def a_data.locs_prefix)
  then show ?thesis
    by (metis \<open>prefix m0 m1\<close> assms(2) data.locs_prefix alocs_def)
qed

lemma check_mupdate_value:
  assumes "mvalue_update is (ml, mdata.Value v, state.Memory sa) = Some yg"
      and "alocs (state.Memory sa) ml = Some (the (alocs (state.Memory sa) ml))"
      and "acheck (state.Memory sa) (the (alocs (state.Memory sa) ml))"
    shows "acheck yg (the (alocs yg ml))"
unfolding a_data.check_def
proof (rule, rule, rule)
  fix x xs
  assume 1: "x |\<in>| the (alocs yg ml)"
     and 2: "yg $ x = Some (mdata.Array xs)"

  from assms(1) obtain l
    where l_def: "mlookup (state.Memory sa) is ml = Some l"
    and "l < length (state.Memory sa)"
    and yg_def: "yg = (state.Memory sa)[l:= mdata.Value v]"
    using mvalue_update_obtain by metis

  then obtain LL
    where "alocs yg ml = Some LL"
      and "LL |\<subseteq>| the (alocs (state.Memory sa) ml)"
    using assms(2) a_data.mupdate_locs_subset[of "(state.Memory sa)" ml yg l]
    by blast

  then have 3: "x |\<in>| the (alocs (state.Memory sa) ml)" using 1 by auto
  moreover have 4: "state.Memory sa $ x = Some (mdata.Array xs)" using 2 yg_def
    apply (auto simp add:nth_safe_def split:if_split_asm)
    by (metis mdata.distinct(1) nth_list_update_eq nth_list_update_neq)

  ultimately have 5:
    "(\<forall>i j i' j' L L'.
        i \<noteq> j \<and>
        xs $ i = Some i' \<and>
        xs $ j = Some j' \<and>
        alocs (state.Memory sa) i' = Some L \<and> alocs (state.Memory sa) j' = Some L'
      \<longrightarrow> L |\<inter>| L' = {||})"
    using assms(3) by (auto simp add:a_data.check_def)

  show "\<forall>i j i' j' L L'.
          i \<noteq> j \<and> xs $ i = Some i' \<and> xs $ j = Some j'
          \<and> alocs yg i' = Some L \<and> alocs yg j' = Some L'
        \<longrightarrow> L |\<inter>| L' = {||}"
  proof (rule, rule, rule, rule, rule, rule, rule, (erule conjE)+)
    fix i j i' j' L L'
    assume "i \<noteq> j"
       and "xs $ i = Some i'"
       and "xs $ j = Some j'"
       and L_def: "alocs yg i' = Some L"
       and L'_def: "alocs yg j' = Some L'"
    have 1: "alocs (state.Memory sa) i' = Some (the (alocs (state.Memory sa) i'))"
      by (metis (lifting) 3 4 \<open>xs $ i = Some i'\<close> assms(2) option.sel a_data.locs_def a_data.locs_safe_in_locs)
    have 2: "alocs (state.Memory sa) j' = Some (the (alocs (state.Memory sa) j'))"
      by (metis (lifting) 3 4 \<open>xs $ j = Some j'\<close> assms(2) option.sel a_data.locs_def a_data.locs_safe_in_locs)
    from 1 have "L |\<subseteq>| the (alocs (state.Memory sa) i')"
      using L_def yg_def \<open>l < length (state.Memory sa)\<close>
        a_data.mupdate_locs_subset[of "(state.Memory sa)" i' yg l v]
      by auto
    moreover from 2 have "L' |\<subseteq>| the (alocs (state.Memory sa) j')"
      using L'_def yg_def \<open>l < length (state.Memory sa)\<close>
        a_data.mupdate_locs_subset[of "(state.Memory sa)" j' yg l v] 
      by auto
    moreover have
      "the (alocs (state.Memory sa) i') |\<inter>| the (alocs (state.Memory sa) j') = {||}"
      using 1 2 5 \<open>i \<noteq> j\<close> \<open>xs $ i = Some i'\<close> \<open>xs $ j = Some j'\<close> by auto
    ultimately show "L |\<inter>| L' = {||}" by auto
  qed
qed

lemma check_mupdate:
  assumes "mvalue_update is1 (l1, v, m0) = Some m1"
      and "mlookup m0 is2 l2 = Some l2'"
      and "m0 $ l2' = Some v"
      and "alocs m0 l1 = Some (the (alocs m0 l1))"
      and "acheck m0 (the (alocs m0 l1))"
      and "alocs m0 l2 = Some (the (alocs m0 l2))"
      and "acheck m0 (the (alocs m0 l2))"
      and "the (alocs m0 l1) |\<inter>| the (alocs m0 l2) = {||}"
    shows "acheck m1 (the (alocs m1 l1))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 is1 l1 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=v]" using mvalue_update_obtain by metis
  then have 0: "m1 $ l = m0 $ l2'" by (simp add: assms(3))
  moreover have 2: "alocs_safe {||} m0 l = Some (the (alocs_safe {||} m0 l))"
    by (metis assms(4) l_def option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have 4: "\<forall>l|\<in>|the (alocs_safe {||} m0 l1) |-| the (alocs_safe {||} m0 l). m1 $ l = m0 $ l"
  proof
    fix l' assume "l' |\<in>|the (alocs_safe {||} m0 l1) |-| (the (alocs_safe {||} m0 l))"
    moreover have "l |\<notin>| the (alocs_safe {||} m0 l1) |-| (the (alocs_safe {||} m0 l))"
      by (meson "2" fminusD2 a_data.locs_safe_subs)
    ultimately have "l \<noteq> l'" by blast
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by (simp)
  qed
  moreover have "\<forall>l|\<in>|the (alocs_safe {||} m0 l2). m1 $ l = m0 $ l"
  proof
    fix l' assume "l'|\<in>| the (alocs_safe {||} m0 l2)"
    moreover have "l |\<in>| the (alocs_safe {||} m0 l1)"
      by (metis assms(4) l_def a_data.locs_def a_data.locs_mlookup)
    ultimately have "l \<noteq> l'" using assms(5,8)
      by (metis fempty_iff finterI a_data.locs_def)
    then show "m1 $ l' = m0 $ l'" unfolding nth_safe_def using ** by simp
  qed
  then have 5: "\<forall>l|\<in>|the (alocs_safe {||} m0 l2'). m1 $ l = m0 $ l"
    by (metis assms(2,6) fsubsetD option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have 6: "locations m0 is1 l1 = Some (the (locations m0 is1 l1))"
    by (simp add: l_def mlookup_locations_some)
  moreover have "the (locations m0 is1 l1) |\<inter>| the (alocs_safe {||} m0 l2) = {||}"
    by (smt (verit, best) "6" assms(4,8) finter_absorb1 finter_assoc finter_commute finter_fempty_left a_data.locs_def
        a_data.locs_locations)
  then have 7: "the (locations m0 is1 l1) |\<inter>| the (alocs_safe {||} m0 l2') = {||}"
    by (smt (verit, best) assms(2,6) fsubset_fempty inf.cobounded1 inf.cobounded2 inf.order_iff inf_mono
        option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  moreover have "l |\<notin>| the (alocs_safe {||} m0 l2)" using assms(5)
    by (metis assms(4,8) disjoint_iff_fnot_equal l_def a_data.locs_def a_data.locs_mlookup)
  then have 8: "l |\<notin>| the (alocs_safe {||} m0 l2')"
    by (metis assms(2,6) finterD1 inf.absorb_iff2 option.sel a_data.locs_def
        a_data.locs_safe_mlookup_locs)
  moreover have 9: "alocs_safe {||} m0 l1 = Some (the (alocs_safe {||} m0 l1))"
    by (metis assms(4) a_data.locs_def)
  ultimately obtain L where L_def: "alocs_safe {||} m1 l1 = Some L"
    using a_data.update_some_obtains_locs[OF l_def 0 _ 2 _ 4 5 _ 6 7 8 ] assms(5)
    by (metis assms(2,6) finter_fempty_left option.sel a_data.locs_def a_data.locs_safe_mlookup_locs)
  
  moreover from 9 have 9: "data.locs_safe {||} m0 l1 = Some (the (data.locs_safe {||} m0 l1))"
    by (metis alocs_safe_def)
  moreover from 2 have 2: "data.locs_safe {||} m0 l = Some (the (alocs_safe {||} m0 l))"
    by (metis alocs_safe_def)
  moreover have 10: "data.locs_safe {||} m0 l2' = Some (the (data.locs_safe {||} m0 l2'))"
    by (metis assms(2,6) data.locs_safe_mlookup_locs alocs_def alocs_safe_def option.sel
        a_data.locs_def)
  moreover from 4 have 4: "\<forall>l|\<in>|the (data.locs_safe {||} m0 l1) |-| the (alocs_safe {||} m0 l). m1 $ l = m0 $ l"
    by (metis alocs_safe_def)
  moreover from 5 have 5: "\<forall>l|\<in>|the (data.locs_safe {||} m0 l2'). m1 $ l = m0 $ l"
    by (metis alocs_safe_def)
  moreover have 11: "storage_data.check m0 (the (data.locs_safe {||} m0 l1))"
    by (metis assms(5) acheck_def data.locs_def alocs_def)
  moreover have 12: "storage_data.check m0 (the (data.locs_safe {||} m0 l2'))"
  proof -
    from assms(7) have "storage_data.check m0 (the (alocs m0 l2))"
      by (simp add: acheck_def)
    with 10 show ?thesis
      by (metis (no_types, lifting) assms(2,6) acheck_def data.locs_safe_mlookup_locs alocs_def
          alocs_safe_def option.sel a_data.check_subs a_data.locs_def)
  qed
  moreover from L_def have 13: "data.locs_safe {||} m1 l1 = Some L"
    by (metis alocs_safe_def)
  moreover have "the (data.locs_safe {||} m0 l1) |-| the (alocs_safe {||} m0 l) |\<inter>| the (data.locs_safe {||} m0 l2') =
    {||}"
  proof -
    from assms(8) have "the (data.locs_safe {||} m0 l1) |\<inter>| the (data.locs_safe {||} m0 l2) = {||}"
      by (simp add: alocs_safe_def a_data.locs_def)
    then have "the (data.locs_safe {||} m0 l1) |\<inter>| the (data.locs_safe {||} m0 l2') = {||}"
      by (smt (verit, best) "10" assms(2,6) disjoint_iff_fnot_equal fsubsetD alocs_safe_def locs_storage_safe_def
          a_data.locs_def storage_data.mlookup_locs_subs)
    then show ?thesis by blast
  qed
  ultimately have "storage_data.check m1 L" using data.check_update [OF l_def 0 9 2 10 4 5 11 12 13] by blast
  then show ?thesis
    by (simp add: "13" acheck_def data.locs_def alocs_def)
qed

lemma check_mupdate2:
  assumes "mvalue_update is (l0, v, m0) = Some m1"
      and "alocs m0 l1 = Some (the (alocs m0 l1))"
      and "the (mlookup m0 is l0) |\<notin>| the (alocs m0 l1)"
      and "acheck m0 (the (alocs m0 l1))"
    shows "acheck m1 (the (alocs m1 l1))"
proof -
  from assms(1) obtain l
    where l_def: "mlookup m0 is l0 = Some l"
    and *: "l < length m0"
    and **: "m1 = m0[l:=v]" using mvalue_update_obtain by metis
  
  from assms(2) obtain L where L_def: "alocs m0 l1 = Some L" by blast
  moreover from assms(3) l_def * ** have "\<forall>l'|\<in>|L. m1 $ l' = m0 $ l'" unfolding nth_safe_def apply (auto split:if_split)
    by (metis calculation nth_list_update_neq option.sel)
  ultimately have *: "alocs m1 l1 = Some L" using assms(3) a_data.locs_same[of m0 l1 L] by blast
  then have "\<forall>l|\<in>|the (alocs m0 l1). m0 $ l = m1 $ l" using L_def
    by (simp add: \<open>\<forall>l'|\<in>|L. m1 $ l' = m0 $ l'\<close>)
  then have "acheck m1 (the (alocs m0 l1))" using a_data.check_check[OF assms(4,2)] by blast
  then show ?thesis using * L_def by auto 
qed

text \<open>Needs to be used manually\<close>
lemma isValue_isArray_all:
  assumes "mdata.is_Value aa"
      and "mlookup m0 xs l0 = Some ya"
      and "m0 $ ya = Some aa"
      and "acopy m0 l0 = Some cd"
      and "adata.is_Array (the (alookup xs cd))"
  shows thesis
proof -
  from copy_memory_alookup_obtains[OF _ assms(2), of "{||}" cd]
  obtain cd' where "acopy_safe {||} m0 ya = Some cd'" and "alookup xs cd = Some cd'"
    using assms(4) unfolding a_data.copy_def by blast
  with assms(1,3) have "adata.is_Value cd'" by (auto simp add:case_memory_def split:option.split mdata.split_asm)
  then show ?thesis using assms
    by (simp add: \<open>alookup xs cd = Some cd'\<close> adata.distinct_disc(1))
qed

subsection \<open>Proof Method\<close>

method slookup uses lookup = solves\<open>rule lookup | (simp(no_asm), rule lookup)\<close>

method mc uses lookup
  = (erule locs_locs_minit_1)
  | (erule locs_locs_minit_2)
  | (erule locs_locs_disj_minit)
  | (erule locs_disj_minit)
  | (erule locs_disj_mupdate, assumption, assumption)
  | (erule locs_some_mupdate_value)
  | (erule locs_some_mupdate_1, assumption, assumption)
  | (erule locs_some_mupdate_2)
  | (erule minit_copy, solves \<open>simp add:prefix_def\<close>)
  | (erule copy_minit)
  | (erule copy_mupdate_value)
  | (erule copy_mupdate, solves\<open>simp\<close>, solves\<open>simp\<close>)
  | (erule copy_memory_mupdate)
  | (erule check_locs_minit_1)
  | (erule check_locs_minit_2)
  | (erule check_mupdate_value)
  | (erule check_mupdate, solves\<open>simp\<close>, solves\<open>simp\<close>)
  | (erule nth_some, solves\<open>simp\<close>)
  | (erule mlookup_mupdate, solves\<open>simp\<close>)
  | (erule mlookup_some_minit, (slookup lookup: lookup)?)
  | (erule mlookup_some_minit2)
  | (erule mlookup_nth_mupdate)
  | (erule mlookup_neq_minit, solves\<open>simp\<close>)
  | (erule mlookup_neq_minit22, assumption)
  | (erule mlookup_neq_mupdate, assumption, assumption, assumption, solves\<open>simp\<close>)
  | (erule mlookup_neq_mupdate2, assumption, assumption, assumption, solves\<open>simp\<close>)
  | (erule mlookup_loc_minit, (slookup lookup: lookup)?)
  | (erule mlookup_loc_minit2)
  | (erule mlookup_nin_loc_minit, solves\<open>simp\<close>)
  | (erule mlookup_locs_minit)
  | (erule mlookup_locs_minit2)
  | (erule locations_minit, (slookup lookup: lookup)?)
  | (erule locations_minit1)
  | (erule locations_mupdate)
  | (erule mlookup_locations_minit_1, (slookup lookup: lookup)?)
  | (erule mlookup_locations_minit_2, (slookup lookup: lookup)?)
  | (erule mlookup_locations_minit_21, (slookup lookup: lookup)?)
  | (erule mlookup_locations_minit_3)
  | (erule mlookup_locations_mupdate_1, assumption, assumption, solves\<open>simp\<close>)
  | (erule mlookup_locations_mupdate_2, assumption, assumption, solves\<open>simp\<close>)
  | (erule check_mupdate2)

end