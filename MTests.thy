theory MTests
  imports Mcalc
begin

(* TODOS:
  1) Refactor Mcalc (Categorize lemmas and rename some, move some to Memory)
  2) Refactor MTest (Some of the proofs may be simplified)
  3) Create examples for larger arrays (size 20)
  4) Finish examples for dynamic arrays
  5) Use dodo everywhere (instead of ooo)
*)

section \<open>Helper\<close>

abbreviation A0 where
"A0 x \<equiv> (\<exists>v0 v1 v2 v3 v4. x = [sdata.Value (Uint v0), sdata.Value (Uint v1), sdata.Value (Uint v2), sdata.Value (Uint v3), sdata.Value (Uint v4)])"

abbreviation A1 where
"A1 x \<equiv> (\<exists>ar0 is_Array1 is_Array2 ar3 ar4. x = [sdata.Array ar0, sdata.Array is_Array1, sdata.Array is_Array2, sdata.Array ar3, sdata.Array ar4]
          \<and> A0 ar0 \<and> A0 is_Array1 \<and> A0 is_Array2 \<and> A0 ar3 \<and> A0 ar4)"

abbreviation A2 where
"A2 x \<equiv> (\<exists>ar0 is_Array1 is_Array2 ar3 ar4. x = [sdata.Array ar0, sdata.Array is_Array1, sdata.Array is_Array2, sdata.Array ar3, sdata.Array ar4]
          \<and> A1 ar0 \<and> A1 is_Array1 \<and> A1 is_Array2 \<and> A1 ar3 \<and> A1 ar4)"

lemma p_0:
assumes "x < Suc 0" and "P 0"
  shows "P x"
  using assms
  by simp

lemma p_suc:
assumes "x < y" and "y = Suc z" and "x < z \<Longrightarrow> P x" and "P z" 
  shows "P x"
  using assms
  using not_less_less_Suc_eq by auto

method exhaust = ((erule p_0, simp) | (erule p_suc, simp))

lemma dlookup_array2:
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
      and "i < 5"
    shows "\<exists>v0 v1 v2 v3 v4. dlookup [Uint (word_of_nat i)] x = Some (sdata.Array [sdata.Value (Uint v0), sdata.Value (Uint v1), sdata.Value (Uint v2), sdata.Value (Uint v3), sdata.Value (Uint v4)])"
  apply (insert assms)
  by (rule p_suc, assumption, simp, auto simp add:dlookup.simps)+

lemma dlookup_array3:
  assumes "\<exists>ar. y = sdata.Array ar \<and> A2 ar"
      and "j < 5"
    shows "\<not> Option.is_none (dlookup [Uint (word_of_nat j)] y)"
  using assms
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  done

lemma dlookup_array4:
  assumes "\<exists>ar. y = sdata.Array ar \<and> A2 ar"
      and "j < 5"
      and "k < 5"
    shows "\<not> Option.is_none (dlookup [Uint (word_of_nat j),Uint (word_of_nat k)] y)"
  using assms
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  done

lemma is_Array1:
  assumes "\<exists>ar. y = sdata.Array ar \<and> A2 ar"
      and "j < 5"
      shows "sdata.is_Array (the (dlookup [Uint (word_of_nat j)] y))"
  using assms
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  done

lemma is_Array2:
  assumes "\<exists>ar. y = sdata.Array ar \<and> A2 ar"
      and "j < 5"
      and "k < 5"
    shows "sdata.is_Array (the (dlookup [Uint (word_of_nat j),Uint (word_of_nat k)] y))"
  using assms
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  done

section \<open>Assign 1\<close>

(*
  // precondition i < length x
  // postcondition z[i] = y /\ forall j < length x. j noteq i --> z[j] = x[j]
  function simple1(uint8[5] memory x, uint8 i, uint8 y) public returns (uint8[5] memory z) {
      x[i] = y;
      return x;
  }
*)

lemma (in Contract)
  assumes "\<exists>ar. x = sdata.Array ar \<and> A0 ar"
      and "unat i < 5"
    shows
         "wp (do {
            minit x (STR ''x'');
            assign_stack_monad (STR ''x'') [sint_monad i] (sint_monad y)
          })
          (pred_memory (STR ''x'')
            (\<lambda>cd.
              dlookup [Uint i] cd = Some (sdata.Value (Uint y)) \<and>
              (\<forall>j<5. j \<noteq> unat i \<longrightarrow> dlookup [Uint (word_of_nat j)] cd = Some (the (dlookup [Uint  (word_of_nat j)] x)))))
          (K (K True))
          s"
  apply wp+
  apply (auto simp add: pred_memory_def)
  apply (rule pred_some_copy_memory)
  apply mc+
  apply (rule conjI)
  using assms apply (auto simp add:dlookup.simps split:nat.split)[1]
  apply rule
  apply rule
  apply exhaust+
  using assms by (auto simp add:dlookup.simps split:nat.split)

section \<open>Assign 2\<close>

(*
  // precondition i < 5 /\ j < 5
  // postcondition forall i' < 5. z[i][i'] = y[j][i'] /\ forall i' < 5. i' noteq i --> forall i'' < 5. z[i'][i''] = x[i'][i'']
  function assign2(uint8[5][5] memory x, uint8 i, uint8 j, uint8[5][5] memory y) public returns (uint8[5][5] memory z) {
      x[i] = y[j];
      return x;
  }
*)

definition P where "P i j s \<equiv> (case (Stack s) $$ (STR ''x'') of
        Some (kdata.Memory l) \<Rightarrow>
          pred_some
            (\<lambda>cd. case (Stack s) $$ (STR ''y'') of
              Some (kdata.Memory l') \<Rightarrow>
                (pred_some
                  (\<lambda>cd'. (\<forall>i'<5. i' \<noteq> i \<longrightarrow> dlookup [Uint (word_of_nat i), Uint  (word_of_nat i')] cd = Some (the (dlookup [Uint (word_of_nat j), Uint  (word_of_nat i')] cd'))))
                  (copy_memory_calldata (State.Memory s) l'))
             | _ \<Rightarrow> False)
            (copy_memory_calldata (State.Memory s) l)
      | _ \<Rightarrow> False)"

lemma assign2:
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A1 ar"
      and "i < 5"
      and "j < 5"
    shows "\<forall>i'<5. i' \<noteq> i \<longrightarrow>
            dlookup [Uint (word_of_nat i), Uint (word_of_nat i')] (the (dlookup [Uint (word_of_nat j)] y
              \<bind> (\<lambda>cd. updateCalldata [Uint (word_of_nat i)] cd x)))
            = Some (the (dlookup [Uint (word_of_nat j), Uint (word_of_nat i')] y))"
  apply rule
  apply rule
  apply exhaust+
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  by (solves\<open>auto simp add:dlookup.simps\<close>)+

lemma (in Contract)
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
    and "\<exists>ar. y = sdata.Array ar \<and> A1 ar"
    and "i < 5"
    and "j < 5"
  shows
     "wp (do {
        minit x (STR ''x'');
        minit y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad (word_of_nat i)] (stackLookup (STR ''y'') [sint_monad (word_of_nat j)])
      })
      (\<lambda>_. P i j)
      (K (K True))
      s"
  apply wp+
  apply auto
  apply (drule is_Array_minit, simp, simp)
  using dlookup_array2[OF assms(2,4)] apply auto[2]
  apply wp+
  unfolding P_def apply auto
  apply (rule pred_some_copy_memory)
  apply mc+
  apply (rule pred_some_copy_memory)
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using assign2[OF assms] by blast

section \<open>Assign 3\<close>

(*
    // precondition i < 5 /\ j < 5 /\ k < 5
    // postcondition  z[i][k]=l
    function aliasing1(uint8[5][5] memory x, uint8 i, uint8 j, uint8[5][5] memory y, uint8 k, uint8 l) public returns (uint8[5][5] memory z) {
        x[i] = y[j];
        y[j][k] = l;
        return x;
    }
*)

lemma assign3:
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A1 ar"
      and "i < 5"
      and "j < 5"
      and "k < 5"
    shows "dlookup [Uint (word_of_nat i), Uint (word_of_nat k)]
            (the
              (updateCalldata ([Uint (word_of_nat i)] @ [Uint (word_of_nat k)])
                (sdata.Value (Uint l))
                (the (dlookup [Uint (word_of_nat j)] y
                  \<bind> (\<lambda>cd. updateCalldata [Uint (word_of_nat i)] cd x)))))
           = Some (sdata.Value (Uint l))"
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  by (solves\<open>auto simp add:dlookup.simps\<close>)+

lemma (in Contract)
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A1 ar"
      and "i < 5"
      and "j < 5"
      and "k < 5"
    shows
     "wp (do {
        minit x (STR ''x'');
        minit y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad (word_of_nat i)] (stackLookup (STR ''y'') [sint_monad (word_of_nat j)]);
        assign_stack_monad (STR ''y'') [sint_monad (word_of_nat j), sint_monad (word_of_nat k)] (sint_monad l)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. dlookup [Uint (word_of_nat i), Uint (word_of_nat k)] cd = Some (sdata.Value (Uint l))))
      (K (K True))
      s"
  apply wp+
  apply (auto)
  apply (drule is_Array_minit, simp, simp)
  using dlookup_array2[OF assms(2,4)] apply auto[2]
  apply wp+
  apply (auto simp add: pred_memory_def)

  (*Aliasing*)
  apply (drule_tac ?xs1.0 = "[Uint (word_of_nat j)]" and ?l1.0=la in aliasing, simp, simp)
  apply mc+
  using dlookup_array2[OF assms(2,4)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(2,4)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply (rule pred_some_copy_memory)
  apply mc+
  using assign3[OF assms] by blast

section \<open>Assign 4\<close>

(*
    // precondition i < 5 /\ j < 5 /\ k < 5
    // postcondition z[j][k]=l
    function aliasing2(uint8[5][5] memory x, uint8 i, uint8 j, uint8[5][5] memory y, uint8 k, uint8 l) public returns (uint8[5][5] memory z) {
        x[i] = y[j];
        x[i][k] = l;
        return y;
    }
*)

lemma assign4:
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A1 ar"
      and "i < 5"
      and "j < 5"
      and "k < 5"
    shows "dlookup [Uint (word_of_nat j), Uint (word_of_nat k)]
        (the (updateCalldata [Uint (word_of_nat j), Uint (word_of_nat k)] (sdata.Value (Uint l)) y)) =
       Some (sdata.Value (Uint l))"
  apply (insert assms)
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  apply (solves\<open>auto simp add:dlookup.simps\<close>)+
  apply exhaust+
  by (solves\<open>auto simp add:dlookup.simps\<close>)+

lemma (in Contract)
  assumes "\<exists>ar. x = sdata.Array ar \<and> A1 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A1 ar"
      and "i < 5"
      and "j < 5"
      and "k < 5"
    shows
     "wp (do {
        minit x (STR ''x'');
        minit y (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad (word_of_nat i)] (stackLookup (STR ''y'') [sint_monad (word_of_nat j)]);
        assign_stack_monad (STR ''x'') [sint_monad (word_of_nat i), sint_monad (word_of_nat k)] (sint_monad l)
      })
      (pred_memory (STR ''y'') (\<lambda>cd. dlookup [Uint (word_of_nat j), Uint (word_of_nat k)] cd = Some (sdata.Value (Uint l))))
      (K (K True))
      s"
  apply wp+
  apply (auto)
  apply (drule is_Array_minit, simp, simp)
  using dlookup_array2[OF assms(2,4)] apply auto[2]
  apply wp+
  apply (auto simp add: pred_memory_def)

  (*Aliasing*)
  apply (drule_tac ?xs = "[Uint (word_of_nat i), Uint (word_of_nat k)]" and ?xs1.0 = "[Uint (word_of_nat i)]" in aliasing2, simp, simp)
  apply mc+
  using dlookup_array2[OF assms(2,4)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(2,4)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply (rule pred_some_copy_memory)
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using dlookup_array2[OF assms(1,3)] apply auto[1]
  apply mc+
  using assign4[OF assms] by simp

section \<open>Assign 5\<close>

(*
    // precondition i < 5 /\ j < 5 /\ k < 5 /\ l < 5 /\ m < 5 /\ n < 5
    // postcondition a[i][k][n]=o
    function aliasing3(uint8[5][5][5] memory x, uint8[5][5][5] memory y, uint8[5][5][5] memory z, uint8 i, uint8 j, uint8 k, uint8 l, uint8 m, uint8 n, uint8 o) public returns (uint8[5][5] memory a) {
        x[i] = y[j];
        y[j][k] = z[l][m];
        z[l][m][n] = o;
        assert (x[2][3][1] == 1);
    }
*)

lemma (in Contract) assign5:
  assumes "\<exists>ar. x = sdata.Array ar \<and> A2 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A2 ar"
      and "\<exists>ar. z = sdata.Array ar \<and> A2 ar"
      and "i < 5"
      and "j < 5"
      and "k < 5"
      and "l < 5"
      and "m < 5"
      and "n < 5"
  shows "dlookup [Uint (word_of_nat i), Uint (word_of_nat k), Uint (word_of_nat n)]
        (the (updateCalldata [Uint (word_of_nat i), Uint (word_of_nat k), Uint (word_of_nat n)]
               (sdata.Value (Uint p))
               (the (dlookup [Uint (word_of_nat l), Uint (word_of_nat m)] z \<bind>
                     (\<lambda>cd. updateCalldata [Uint (word_of_nat i), Uint (word_of_nat k)] cd
                            (the (dlookup [Uint (word_of_nat j)] y \<bind>
                                  (\<lambda>cd. updateCalldata [Uint (word_of_nat i)] cd x)))))))) =
       Some (sdata.Value (Uint p))"
proof -
  have "\<exists>d. dlookup [Uint (word_of_nat j)] y = Some (sdata.Array d) \<and> A1 d"
    apply (insert assms(2,5))
    apply (exhaust)+
    by (auto simp add:dlookup.simps)
  then obtain d
    where d_def: "dlookup [Uint (word_of_nat j)] y = Some (sdata.Array d)"
      and 1: "A1 d"
    by auto
  have "\<exists>d1. updateCalldata [Uint (word_of_nat i)] (sdata.Array d) x = Some (sdata.Array d1) \<and> A2 d1"
    apply (insert 1 assms(1,4))
    apply (exhaust)+
    by (auto simp add:dlookup.simps)

   then obtain d1
     where d1_def: "updateCalldata [Uint (word_of_nat i)] (sdata.Array d) x = Some (sdata.Array d1)"
       and 2: "A2 d1"
     by auto

  have "\<exists>d2. dlookup [Uint (word_of_nat l), Uint (word_of_nat m)] z = Some (sdata.Array d2) \<and> A0 d2"
    apply (insert assms(3,7,8))
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    done
  then obtain d2
    where d2_def: "dlookup [Uint (word_of_nat l), Uint (word_of_nat m)] z = Some (sdata.Array d2)"
      and 3: "A0 d2"
    by blast

  have "\<exists>d3. updateCalldata [Uint (word_of_nat i), Uint (word_of_nat k)] (sdata.Array d2) (sdata.Array d1) = Some (sdata.Array d3) \<and> A2 d3"
    apply (insert 2 3 assms(4,6))
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    by (auto simp add:dlookup.simps)
  then obtain d3
    where d3_def: "updateCalldata [Uint (word_of_nat i), Uint (word_of_nat k)] (sdata.Array d2) (sdata.Array d1) = Some (sdata.Array d3)"
      and 4: "A2 d3"
    by auto

    have "\<exists>d4. updateCalldata [Uint (word_of_nat i), Uint (word_of_nat k), Uint (word_of_nat n)]
               (sdata.Value (Uint p)) (sdata.Array d3) = Some (sdata.Array d4)
    \<and> dlookup [Uint (word_of_nat i), Uint (word_of_nat k), Uint (word_of_nat n)] (sdata.Array d4) = Some (sdata.Value (Uint p))"
    apply (insert 4 assms(4,6,9))
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    apply (exhaust)+
    apply (auto simp add:dlookup.simps)
    done

  then show ?thesis using d_def d1_def d2_def d3_def
    by auto
qed

lemma (in Contract)
  assumes "\<exists>ar. x = sdata.Array ar \<and> A2 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> A2 ar"
      and "\<exists>ar. z = sdata.Array ar \<and> A2 ar"
      and "i < 5"
      and "j < 5"
      and "k < 5"
      and "l < 5"
      and "m < 5"
      and "n < 5"
    shows
     "wp (do {
        minit x (STR ''x'');
        minit y (STR ''y'');
        minit z (STR ''z'');
        assign_stack_monad (STR ''x'') [sint_monad (word_of_nat i)] (stackLookup (STR ''y'') [sint_monad (word_of_nat j)]);
        assign_stack_monad (STR ''y'') [sint_monad (word_of_nat j), sint_monad (word_of_nat k)] (stackLookup (STR ''z'') [sint_monad (word_of_nat l), sint_monad (word_of_nat m)]);
        assign_stack_monad (STR ''z'') [sint_monad (word_of_nat l), sint_monad (word_of_nat m), sint_monad (word_of_nat n)] (sint_monad p)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. dlookup [Uint (word_of_nat i), Uint (word_of_nat k), Uint (word_of_nat n)] cd = Some (sdata.Value (Uint p))))
      (K (K True))
      s"
  apply wp+
  apply (auto)
  defer defer
  apply (auto simp add: pred_memory_def)
  apply wp+
  apply (auto simp add: pred_memory_def)
  defer
  apply wp+
  apply (auto simp add: pred_memory_def)

  apply (drule_tac ?xs1.0 = "[Uint (word_of_nat j)]" and ?l1.0=la and ?l2.0=x1 in aliasing, simp, simp)
  apply (mc lookup: dlookup_array3[OF assms(2,5)] dlookup_array3[OF assms(1,4)])+

  apply (drule_tac ?xs1.0 = "[Uint (word_of_nat l), Uint (word_of_nat m)]" and ?l1.0=laa and ?l2.0=x1 in aliasing, simp, simp)
  apply (mc lookup: dlookup_array3[OF assms(2,5)] dlookup_array3[OF assms(1,4)] dlookup_array4[OF assms(3,7,8)] dlookup_array4[OF assms(2,5,6)] dlookup_array4[OF assms(1,4,6)])+

  apply (rule pred_some_copy_memory)
  apply (mc lookup: dlookup_array3[OF assms(2,5)] dlookup_array3[OF assms(1,4)] dlookup_array4[OF assms(3,7,8)] dlookup_array4[OF assms(2,5,6)] dlookup_array4[OF assms(1,4,6)])+
  defer
  apply (erule isValue_isArray_all, assumption, assumption)
  apply mc+
  defer
  apply wp+
  apply (auto simp add: pred_memory_def)
  apply (erule isValue_isArray_all, assumption, assumption)
  apply mc+
  defer
  apply (erule isValue_isArray_all, assumption, assumption)
  apply (mc lookup: dlookup_array3[OF assms(2,5)] dlookup_array3[OF assms(1,4)] dlookup_array4[OF assms(3,7,8)] dlookup_array4[OF assms(2,5,6)] dlookup_array4[OF assms(1,4,6)])+
  apply (rule is_Array2[OF assms(3,7,8)])
  defer
  apply (rule is_Array1[OF assms(2,5)])
  apply (rule is_Array1[OF assms(2,5)])
  apply (rule assign5[OF assms])
  done

section \<open>Dynamic Arrays\<close>

lemma thethe:
  assumes "updateCalldata ys v cd = Some X"
  and "Q (dlookup xs X)"
shows "Q (dlookup xs (the (updateCalldata ys v cd)))"
  using assms
  by simp

lemma the1:
  assumes "x = Some y'"
      and "y y' = Some z"
  shows "the (x \<bind> y) = z"
  using assms by simp

abbreviation DA0 where "DA0 a \<equiv> \<forall>x<length a. \<exists>v. a!x = sdata.Value (Uint v)"
abbreviation DA1 where "DA1 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = sdata.Array a' \<and> DA0 a'"
abbreviation DA2 where "DA2 a \<equiv> \<forall>x<length a. \<exists>a'. a!x = sdata.Array a' \<and> DA1 a'"

lemma ccc:
  assumes "to_nat i = Some i'"
      and "cd = (sdata.Array xs)"
      and "i' < length xs"
      and "updateCalldata is v (xs ! i') = Some cd'"
    shows "updateCalldata (i # is) v cd = (Some \<circ> sdata.Array \<circ> list_update xs i') cd'"
  using assms by simp

lemma hhh:
  assumes "DA2 (sdata.ar z)"
      and "unat l < length (sdata.ar z)"
      and "unat m < length (sdata.ar ((sdata.ar z) ! (unat l)))"
    shows "sdata.ar ((sdata.ar z) ! unat l) ! unat m = sdata.Array (sdata.ar (sdata.ar ((sdata.ar z) ! unat l) ! unat m))"
proof -
  from assms(1,2) obtain a' where "(sdata.ar z)!unat l = sdata.Array a' \<and> DA1 a'" by blast
  then have "a'!unat m = sdata.Array (sdata.ar (a'!unat m))"
    using assms(3) by auto
  then show ?thesis
    by (simp add: \<open>(sdata.ar z) ! unat l = sdata.Array a' \<and> DA1 a'\<close>)
qed

lemma xxx:
  assumes "\<exists>ar. z = sdata.Array ar \<and> DA2 ar"
    shows "z = sdata.Array (sdata.ar z)"
    using assms by auto

lemma yyy:
  assumes "\<exists>ar. z = sdata.Array ar \<and> DA2 ar"
      and "unat l < length (sdata.ar z)"
    shows "sdata.ar z ! unat l = sdata.Array (sdata.ar ( sdata.ar z ! unat l))"
    using assms by auto

lemma zzz:
  assumes "\<exists>ar. y = sdata.Array ar \<and> DA2 ar"
      and "unat i < length (sdata.ar x)"
      and "unat j < length (sdata.ar y)"
    shows "(sdata.ar x)[unat i := sdata.ar y ! unat j] ! unat i
          = sdata.Array (sdata.ar ((sdata.ar x)[unat i := sdata.ar y ! unat j] ! unat i))"
    using assms by auto

lemma zazas:
  assumes "unat i < length (sdata.ar x)"
    shows "(sdata.ar x)[unat i := sdata.Array ((sdata.ar (sdata.ar y ! unat j))[unat k := sdata.ar (sdata.ar z ! unat l) ! unat m])] ! unat i
          = sdata.Array (sdata.ar ( (sdata.ar x)[unat i := sdata.Array ((sdata.ar (sdata.ar y ! unat j))[unat k := sdata.ar (sdata.ar z ! unat l) ! unat m])] ! unat i))"
    using assms by auto

lemma zazas2:
  assumes "\<exists>ar. z = sdata.Array ar \<and> DA2 ar"
      and "unat i < length (sdata.ar x)"
      and "unat k < length (sdata.ar ((sdata.ar y) ! (unat j)))"
      and "unat l < length (sdata.ar z)"
      and "unat m < length (sdata.ar ((sdata.ar z) ! (unat l)))"
    shows "sdata.ar ((sdata.ar x)[unat i := sdata.Array ((sdata.ar (sdata.ar y ! unat j))[unat k := sdata.ar (sdata.ar z ! unat l) ! unat m])] ! unat i) ! unat k = sdata.Array (sdata.ar (sdata.ar ((sdata.ar x)[unat i := sdata.Array ((sdata.ar (sdata.ar y ! unat j))[unat k := sdata.ar (sdata.ar z ! unat l) ! unat m])] ! unat i) ! unat k))"
    using assms hhh[OF _ assms(4,5)] by auto

method haha uses x
            = (solves\<open>simp\<close>)
            | (rule the1)
            | (rule clookup_empty_some)
            | (rule clookup_nempty_some,simp, (rule x)?)
            | (subst ccc, simp, (rule x)?)

lemma (in Contract) assign6:
  assumes "\<exists>ar. x = sdata.Array ar \<and> DA2 ar"
      and "\<exists>ar. y = sdata.Array ar \<and> DA2 ar"
      and "\<exists>ar. z = sdata.Array ar \<and> DA2 ar"
      and "unat i < length (sdata.ar x)"
      and "unat j < length (sdata.ar y)"
      and "unat k < length (sdata.ar ((sdata.ar y) ! (unat j)))"
      and "unat l < length (sdata.ar z)"
      and "unat m < length (sdata.ar ((sdata.ar z) ! (unat l)))"
      and "unat n < length (sdata.ar (sdata.ar (sdata.ar z ! unat l) ! unat m))"
  shows "dlookup [Uint i, Uint k, Uint n]
        (the (updateCalldata [Uint i, Uint k, Uint n]
               (sdata.Value (Uint p))
               (the (dlookup [Uint l, Uint m] z \<bind>
                     (\<lambda>cd. updateCalldata [Uint i, Uint k] cd
                            (the (dlookup [Uint j] y \<bind>
                                  (\<lambda>cd. updateCalldata [Uint i] cd x)))))))) =
       Some (sdata.Value (Uint p))"
  apply (insert assms)
  apply (haha x: yyy[OF assms(3,7)] xxx[OF assms(3)] xxx[OF assms(1)] xxx[OF assms(2)] zzz[OF assms(2)] zazas[OF assms(4)] zazas2[OF assms(3,4,6,7,8)])+
  apply (auto simp add:dlookup.simps)[1]
  done
end
