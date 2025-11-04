theory ArrayBuilder
imports Solidity_Main Mcalc
begin

abbreviation "items \<equiv> STR ''items''"
abbreviation "owner \<equiv> STR ''owner''"
abbreviation "result  \<equiv> STR ''result''"
abbreviation "counter  \<equiv> STR ''counter''"
abbreviation "i \<equiv> STR ''i''"
abbreviation "itemCount \<equiv> STR ''itemCount''"
abbreviation "Item \<equiv> SType.TEnum [SType.TValue TAddress, SType.TValue TBytes]"

contract ArrayBuilder
  for items: "SType.DArray Item"
  and itemCount : "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor payable
where
  "\<langle>skip\<rangle>"

cfunction getItems external payable
  param owner: "SType.TValue TAddress"
where
  "do {
    create_memory_array result (CType.TValue TSint) (itemCount  ~\<^sub>s [owner ~ []]);
    decl TSint counter;
    decl TSint i;
    while_monad ((i ~ []) \<langle><\<rangle> (storeArrayLength items []))
    (do {
      IF ((items ~\<^sub>s [i ~ [], \<langle>sint\<rangle> 0]) \<langle>=\<rangle> (owner ~ [])) THEN
        do {
          result [counter ~ []] ::= (i ~ []);
          counter [] ::= counter ~ [] \<langle>+\<rangle> \<langle>sint\<rangle> 1
        }
      ELSE
        \<langle>skip\<rangle>;
      i [] ::= i ~ [] \<langle>+\<rangle> \<langle>sint\<rangle> 1
    });
    r \<leftarrow> result ~ [];
    return r
  }"

invariant myInv s
  where "True"
  for "ArrayBuilder"

fun filter_index_prefix_rec where
  "filter_index_prefix_rec 0 0 P xs ys = True"
| "filter_index_prefix_rec 0 (Suc y) P xs ys = False"
| "filter_index_prefix_rec (Suc x) 0 P xs ys = ((\<not> P (xs!x)) \<and> filter_index_prefix_rec x 0 P (butlast xs) [])"
| "filter_index_prefix_rec (Suc x) (Suc y) P xs ys =
    (if P (xs!x) then ys!y = x \<and> filter_index_prefix_rec x y P (butlast xs) (butlast ys)
    else filter_index_prefix_rec x (Suc y) P (butlast xs) ys)"

definition filter_index_prefix where
  "filter_index_prefix P xs ys \<equiv> filter_index_prefix_rec (length xs) (length ys) P xs ys"

definition filter_index where
  "filter_index P xs ys \<equiv> filter_index_prefix P xs ys"

lemma "filter_index ((=) True) [True] [0] = True" by eval
lemma "filter_index ((=) True) [False] [1,2] = False" by eval
lemma "filter_index ((=) True) [False] [] = True" by eval
lemma "filter_index ((=) True) [False,True,False,True,False] [1,3] = True" by eval
lemma "filter_index ((=) True) [False,True,False,True,False] [1,2] = False" by eval

lemma(in ArrayBuilder.arrayBuilder) myInvI2:
  assumes "\<exists>da. fst s items = storage_data.Array da \<and>
    (\<forall>y<length da.
      \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))"
    and "\<exists>mp. fst s itemCount = Map mp \<and> (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si))"
  shows "myInv s"
proof -
  have True by simp
  moreover from assms obtain da where " fst s items = storage_data.Array da \<and>
    (\<forall>y<length da.
      \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)]))"
    by auto
  moreover from assms obtain mp where "fst s itemCount = Map mp \<and> (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si))" by auto
  ultimately show ?thesis using myInvI by blast
qed

definition(in Contract) filter_items where
"filter_items state ow =
  filter_index (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ow) (storage_data.ar (state.Storage state this items))"

definition(in Contract) filter_items_prefix where
"filter_items_prefix n it ow =
  filter_index_prefix (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ow) (take n (storage_data.ar it))"

definition(in Contract) allItems where
"allItems xs ow =
  [x \<leftarrow> xs. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ow]"

definition(in Contract) while_inv where
  "while_inv own state \<equiv>
    pred_some (\<lambda>xs. \<exists>ar. xs = sdata.Array ar \<and> filter_items_prefix (unat (valtype.uint (kdata.vt (state.Stack state $$! i)))) (state.Storage state this items) (valtype.ad (kdata.vt (state.Stack state $$! owner))) (map (unat \<circ> valtype.uint \<circ> sdata.vt) (take (unat (valtype.uint (kdata.vt (state.Stack state $$! counter)))) ar))) (copy_memory_calldata (State.Memory state) (kdata.memloc (state.Stack state $$! result)))
    \<and> check_calldata (state.Memory state) (the (locs_calldata (state.Memory state) (kdata.memloc (state.Stack state $$! result))))
    \<and> state.Stack state $$ owner = Some (kdata.Value own)
    \<and> length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own)) = unat (valtype.uint (storage_data.vt (storage_data.mp (state.Storage state this itemCount) own)))
    \<and> pred_some (\<lambda>xs. length (sdata.ar xs) = length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own))) (copy_memory_calldata (State.Memory state) (kdata.memloc (state.Stack state $$! result)))
    \<and> (\<exists>ml. state.Stack state $$ result = Some (kdata.Memory ml)
        \<and> (\<exists>ma0. state.Memory state ! ml = mdata.Array ma0
            \<and> (\<forall>i<length ma0. \<exists>ix. state.Memory state ! (ma0!i) = mdata.Value (valtype.Uint ix))))
    \<and> (\<exists>x. state.Stack state $$ i = Some (kdata.Value (valtype.Uint x)))
    \<and> (\<exists>x. state.Stack state $$ counter = Some (kdata.Value (valtype.Uint x)))
    \<and> unat (valtype.uint (kdata.vt (state.Stack state $$! counter))) = length (allItems (take (unat (valtype.uint (kdata.vt (state.Stack state $$! i)))) (storage_data.ar (state.Storage state this items))) (valtype.ad own))
    \<and> unat (valtype.uint (kdata.vt (state.Stack state $$! counter))) \<le> unat (valtype.uint (kdata.vt (state.Stack state $$! i)))
    \<and> length (storage_data.ar (state.Storage state this items)) < 2^256
    \<and> (\<exists>da. (state.Storage state this items) = storage_data.Array da \<and>
      (\<forall>y<length da.
        \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])))
    \<and> (\<exists>mp. state.Storage state this itemCount = Map mp \<and>
        (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)))"

lemma(in Contract) while_init:
  assumes "unat (valtype.uint (kdata.vt (state.Stack state $$! i))) = 0"
      and "unat (valtype.uint (kdata.vt (state.Stack state $$! counter))) = 0"
      and "check_calldata (state.Memory state) (the (locs_calldata (state.Memory state) (kdata.memloc (state.Stack state $$! result))))"
      and "state.Stack state $$ owner = Some (kdata.Value own)"
      and "length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own)) = unat (valtype.uint (storage_data.vt (storage_data.mp (state.Storage state this itemCount) own)))"
      and "length (storage_data.ar (state.Storage state this items)) < 2^256"
      and "pred_some (\<lambda>xs. length (sdata.ar xs) = length (allItems (storage_data.ar (state.Storage state this items)) (valtype.ad own))) (copy_memory_calldata (State.Memory state) (kdata.memloc (state.Stack state $$! result)))"
      and "(\<exists>ml. state.Stack state $$ result = Some (kdata.Memory ml)
            \<and> (\<exists>ma0. state.Memory state ! ml = mdata.Array ma0
                \<and> (\<forall>i<length ma0. \<exists>ix. state.Memory state ! (ma0!i) = mdata.Value (valtype.Uint ix))))"
      and "(\<exists>x. state.Stack state $$ i = Some (kdata.Value (valtype.Uint x)))"
      and "(\<exists>x. state.Stack state $$ counter = Some (kdata.Value (valtype.Uint x)))"
      and "copy_memory_calldata
            (state.Memory state)
            (kdata.memloc (Stack state $$! result))
          = Some (sdata.Array (array (unat si) (sdata.Value (Uint 0))))"
      and "(\<exists>da. (state.Storage state this items) = storage_data.Array da \<and>
      (\<forall>y<length da.
        \<exists>em. da ! y = storage_data.Array em \<and>
         (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])))"
      and "(\<exists>mp. state.Storage state this itemCount = Map mp \<and>
        (\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)))"
    shows "while_inv own state"
  using assms unfolding while_inv_def
  by (simp add:pred_some_def filter_items_prefix_def filter_index_prefix_def allItems_def)

definition(in Contract) getItems_post where
  "getItems_post ow start_state return_value end_state \<equiv>
    (pred_some (\<lambda>xs. filter_items end_state ow (map (unat \<circ> valtype.uint \<circ> sdata.vt) (sdata.ar xs))) (copy_memory_calldata (State.Memory end_state) (rvalue.memloc return_value)))"

definition(in Contract) getItems_pre where
  "getItems_pre ow start_state \<equiv>
    length (storage_data.ar (state.Storage start_state this items)) < 2^256 \<and>
    length (allItems (storage_data.ar (state.Storage start_state this items)) ow) = unat (valtype.uint (storage_data.vt (storage_data.mp (state.Storage start_state this itemCount) (valtype.Address ow))))"

lemma(in Contract) ppp:
  fixes mp
  assumes " length
        (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = valtype.ad sstate)
          da) =
       unat (valtype.uint (storage_data.vt (mp sstate)))"
and "length (sdata.ar v'a) = unat (valtype.uint (storage_data.vt (mp sstate)))"
shows "sdata.ar v'a = take (length da) (sdata.ar v'a)"
  using assms
  by (metis length_filter_le take_all_iff)

lemma (in Contract) while_inv_post:
  assumes "while_inv sstate end_state"
      and "ow = valtype.ad (kdata.vt (state.Stack end_state $$! owner))"
      and "rvalue.memloc return_value = kdata.memloc (state.Stack end_state $$! result)"
      and "unat (valtype.uint (kdata.vt (state.Stack end_state $$! i))) \<ge> (length (storage_data.ar (state.Storage end_state this items)))"
    shows "getItems_post ow start_state return_value end_state"
  using assms unfolding while_inv_def getItems_post_def allItems_def pred_some_def filter_items_def filter_items_prefix_def filter_index_def
  by (auto intro: ppp split:option.split_asm option.split)

lemma xxx:
  assumes "mdata.Array ma0 = state.Memory sa ! ml"
  shows "mdata.is_Value (state.Memory sa ! ml) = False"
  using assms
  by (metis mdata.disc(2))

lemma yyy[wpdrules]:
  assumes "kdequals yc (rvalue.Value (Bool True)) = Some (rvalue.Value (Bool False))"
  shows "yc = (rvalue.Value (Bool False))"
  using assms unfolding kdequals_def
  apply (cases yc,auto)
  by (case_tac x4,auto)

lemma yyy1[wpdrules]:
  assumes "kdequals yd (rvalue.Value (Bool True)) = Some (rvalue.Value (Bool True))"
  shows "yd = (rvalue.Value (Bool True))"
  using assms unfolding kdequals_def
  apply (cases yd,auto)
  by (case_tac x4,auto)

lemma yyy2[wpdrules]:
  assumes "kdequals x y = Some (rvalue.Value (Bool True))"
  shows "x = y"
  using assms unfolding kdequals_def
  apply (cases x,auto)
  apply (cases y,auto)
  apply (case_tac x4a,auto)
  by (case_tac x4,auto)+

lemma aaaaaa:     
  assumes "kdplus_safe (rvalue.Value v) (rvalue.Value (Uint 1)) = Some y"
  obtains v' where "v=Uint v'" and "y = rvalue.Value (Uint (v' + 1))" and "unat v' + unat 1 < 2^256"
  using assms unfolding kdplus_safe_def
  apply (cases v)
  by (auto simp add:wpsimps vtplus_safe.simps split:if_split_asm)

lemma zzz:
  assumes "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint (word_of_nat (length a)::256 word))) = Some (rvalue.Value (Bool False))"
    and "length a<2^256"
  shows "\<not> unat x < length a"
  using assms unfolding kdless_def vtless_def
  apply (cases "x <  ((word_of_nat (length a))::256 word)",auto simp add:wpsimps)
  
  subgoal "\<not> x < ((word_of_nat (length a))::256 word) \<Longrightarrow> unat x < length a \<Longrightarrow> False"
  proof -
    assume "\<not> x < ((word_of_nat (length a))::256 word)" and *: "unat x < length a"
    then have "(((word_of_nat (length a))::256 word) \<le> x)" by simp
    then have "(unat ((word_of_nat (length a))::256 word) \<le> unat x)"
      apply (simp add: word_le_nat_alt[where ?'a =256]) done
    moreover from assms(2) have "length a\<le>unat (2^256-1::256 word)" by simp
    ultimately have "length a \<le> unat x" using le_unat_uoi[where ?'a =256, of "length a" _] assms(2) by metis
    then show ?thesis using * by auto
  qed
  done

lemma zzz1:
  assumes "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint (word_of_nat (length a)::256 word))) = Some (rvalue.Value (Bool True))"
    and "length a<2^256"
  shows "unat x < length a"
  using assms unfolding kdless_def vtless_def
  apply (cases "x < ((word_of_nat (length a))::256 word)",auto simp add:wpsimps)
  
  subgoal "x < ((word_of_nat (length a))::256 word) \<Longrightarrow> unat x < length a"
  proof -
    assume "x < ((word_of_nat (length a))::256 word)"
    then have "unat x < (unat ((word_of_nat (length a))::256 word))"
      apply (simp add: word_less_nat_alt[where ?'a =256]) done
    moreover from assms(2) have "length a\<le>unat (2^256-1::256 word)" by simp
    ultimately have "unat x < length a" using le_unat_uoi[where ?'a =256, of "length a" _] assms(2) by metis
    then show ?thesis by auto
  qed
  done

lemma 1[simp]: "length (array x y) = x"
  unfolding array_def
  by simp

lemma 2:
  assumes "Memory.minit (sdata.Array (array (unat si) (sdata.Value (Uint 0)))) [] = (x1, x2)"
  shows "\<exists>ma0. x2 ! x1 = mdata.Array ma0 \<and> (\<forall>i<length ma0. \<exists>ix. x2 ! (ma0 ! i) = mdata.Value (Uint ix))"
  sorry

lemma 3:
  assumes "state.Memory sa ! ml = mdata.Array ma0"
      and "\<forall>i<length ma0. \<exists>ix. state.Memory sa ! (ma0 ! i) = mdata.Value (Uint ix)"
      and "mvalue_update [Uint xa] (ml, mdata.Value (Uint x), state.Memory sa) = Some yg"
  shows "\<exists>ma0. yg ! ml = mdata.Array ma0 \<and> (\<forall>i<length ma0. \<exists>ix. yg ! (ma0 ! i) = mdata.Value (Uint ix))"
  sorry

lemma 4:
  assumes "check_calldata (state.Memory sa) (the (locs_calldata (state.Memory sa) ml))"
      and "mvalue_update [Uint xa] (ml, mdata.Value (Uint x), state.Memory sa) = Some yg"
  shows "check_calldata yg (the (locs_calldata yg ml))"
  sorry

lemma filter1: "n < length x \<Longrightarrow> P (x ! n) \<Longrightarrow> length (filter P (take n x)) < length (filter P x)"
proof (induction x arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Cons.prems(2) by auto
  next
    case (Suc nat)
    then have "nat < length (x)"
      using Cons.prems(1) by auto
    moreover have "P (x ! nat)"
      using Cons.prems(2) Suc by auto
    ultimately have "length (filter P (take nat x)) < length (filter P x)" using Cons.IH by blast
    then show ?thesis
      by (simp add: Suc)
  qed
qed

lemma filter_index_prefix_rec_P:
  assumes "filter_index_prefix_rec (length xs) (length ys) P xs ys"
      and "P x"
    shows "filter_index_prefix_rec (Suc (length xs)) (Suc (length ys)) P (xs @ [x]) (ys @ [length xs])"
  using assms by simp

lemma filter_index_prefix_rec_not_P:
  assumes "filter_index_prefix_rec (length xs) (length ys) P xs ys"
      and "\<not> P x"
    shows "filter_index_prefix_rec (Suc (length xs)) (length ys) P (xs @ [x]) ys"
  using assms by (cases ys,auto)

(*
v'a = index i
ar = static version of memory array result
ad = address of owner of item i which is the same as owner parameter
v' = value of counter
daa = items array
*)
lemma (in Contract) filter_items_prefix_suc_eq:
  fixes ad ar          
  defines "filter_pred x \<equiv> valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad"
  assumes
    "filter_items_prefix (unat v'a) (storage_data.Array daa) ad
      (map (unat \<circ> valtype.uint \<circ> sdata.vt)
        (take (length (filter filter_pred (take (unat v'a) daa))) ar))"
      and "unat v'a < length daa"
      and "length (filter filter_pred daa) = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "length (filter filter_pred (take (unat v'a) daa)) \<le> unat v'a"
      and "unat v' = length (filter filter_pred (take (unat v'a) daa))"
      and "length ar = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "daa $ unat v'a \<bind> slookup [Uint 0] = Some yb"
      and "storage_data.vt yb = Address ad"
      and "length daa < 2^256"
      and
       "\<forall>y<length daa.
         \<exists>em. daa ! y = storage_data.Array em \<and>
          (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])"
    shows
       "\<exists>ara. the (updateCalldata [Uint v'] (sdata.Value (Uint v'a)) (sdata.Array ar)) = sdata.Array ara \<and>
         filter_items_prefix (unat (v'a + 1))
           (storage_data.Array daa)
             ad (map (unat \<circ> valtype.uint \<circ> sdata.vt) (take (unat (v' + 1)) ara))"
proof -
  from assms(3,11) obtain em ad0 bt0
    where *: "daa ! unat v'a = storage_data.Array em"
      and **: "em = [storage_data.Value (Address ad0), storage_data.Value (Bytes bt0)]"
  by auto

  from assms(3,8,9,11)
    have ***: "valtype.ad (storage_data.vt (hd (storage_data.ar (daa ! unat v'a)))) = ad"
    by auto
  then have "unat v' < length ar"
    using filter1[where ?P="filter_pred", of "(unat v'a)" daa] assms(3,4,6,7)
    unfolding filter_pred_def by linarith
  then have
    "length (filter filter_pred (take (unat v'a) daa))
      < unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
    using assms by argo
  moreover have
    "filter_items_prefix (unat (v'a + 1)) (storage_data.Array daa) ad
      (map (unat \<circ> valtype.uint \<circ> sdata.vt)
        (take (unat (v' + 1))
          (ar[length (filter filter_pred (take (unat v'a) daa)) := sdata.Value (Uint v'a)])))"
  proof -
    from assms(2) have
      "filter_index_prefix_rec
        (length (take (unat v'a) (storage_data.ar (storage_data.Array daa))))
        (length
          (map (unat \<circ> valtype.uint \<circ> sdata.vt)
           (take (length (filter filter_pred (take (unat v'a) daa))) ar)))
        filter_pred
        (take (unat v'a) (storage_data.ar (storage_data.Array daa)))
        (map (unat \<circ> valtype.uint \<circ> sdata.vt)
          (take (length (filter filter_pred (take (unat v'a) daa))) ar))"
      unfolding filter_items_prefix_def filter_index_prefix_def filter_pred_def
      by blast
    moreover have "valtype.ad (storage_data.vt (hd (em))) = ad" using * *** by auto
    ultimately have
      "filter_index_prefix_rec
        (Suc (length (take (unat v'a) (storage_data.ar (storage_data.Array daa)))))
        (Suc (length
          (map (unat \<circ> valtype.uint \<circ> sdata.vt)
            (take (length (filter filter_pred (take (unat v'a) daa))) ar))))
        filter_pred
        (take (unat v'a) (storage_data.ar (storage_data.Array daa)) @ [storage_data.Array em])
        (map (unat \<circ> valtype.uint \<circ> sdata.vt)
          (take (length (filter filter_pred (take (unat v'a) daa))) ar) @
          [length (take (unat v'a) (storage_data.ar (storage_data.Array daa)))])"
    using filter_index_prefix_rec_P[where ?P = "filter_pred"] * ***
    unfolding filter_pred_def by presburger
    moreover have
      "length (take (unat (v'a + 1)) (storage_data.ar (storage_data.Array daa)))
     = Suc (length (take (unat v'a) (storage_data.ar (storage_data.Array daa))))"
      using assms(3,10) unat_add_lem[where ?'a=256, of v'a 1] by (simp add:wpsimps)
    moreover have
      "length
         (map (unat \<circ> valtype.uint \<circ> sdata.vt)
           (take (unat (v' + 1))
             (ar[length (filter filter_pred (take (unat v'a) daa)) := sdata.Value (Uint v'a)])))
     = Suc (length
         (map (unat \<circ> valtype.uint \<circ> sdata.vt)
           (take (length (filter filter_pred (take (unat v'a) daa))) ar)))"
    proof -
      from assms(4,7,10) have "length ar < 2 ^ 256"
        using length_filter_le[of "filter_pred" daa] by auto
      then show ?thesis
        using assms(6) \<open>unat v' < length ar\<close> unat_add_lem[where ?'a=256, of v' 1]
        by (simp add:wpsimps)
    qed
    moreover have
      "take (unat (v'a + 1)) (storage_data.ar (storage_data.Array daa))
     = take (unat v'a) (storage_data.ar (storage_data.Array daa)) @ [storage_data.Array em]"
    proof -
      from assms * **
        have "storage_data.ar (storage_data.Array daa) ! unat v'a = storage_data.Array em"
        by simp
      then show ?thesis
        using assms(3,10)
          take_Suc_conv_app_nth[of "unat v'a" "(storage_data.ar (storage_data.Array daa))"]
          unat_add_lem[where ?'a=256, of v'a 1]
        by (simp add:wpsimps)
    qed
    moreover have
      "map (unat \<circ> valtype.uint \<circ> sdata.vt)
         (take (length (filter filter_pred (take (unat v'a) daa))) ar) @
           [length (take (unat v'a) (storage_data.ar (storage_data.Array daa)))]
     = map (unat \<circ> valtype.uint \<circ> sdata.vt)
         (take (unat (v' + 1))
           (ar[length (filter filter_pred (take (unat v'a) daa)) := sdata.Value (Uint v'a)]))"
    proof -
      from assms(4,7,10) have "length ar < 2 ^ 256"
        using length_filter_le[of "filter_pred" daa]
        by auto
      then show ?thesis
        using \<open>unat v' < length ar\<close>
          upd_conv_take_nth_drop[of "unat v'" ar]
          unat_add_lem[where ?'a=256, of v' 1]
          assms(3,6)
        by (simp add:wpsimps)
    qed
    ultimately show ?thesis
      unfolding filter_items_prefix_def filter_index_prefix_def filter_pred_def
      by argo
  qed
  ultimately show ?thesis using assms by (auto simp add:nth_safe_def)
qed

lemma (in Contract) updateCalldata_length:
  fixes ar ad
  defines "filter_pred x \<equiv> valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad"
  assumes "unat v'a < length daa"
      and "length (filter filter_pred daa) = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "unat v' = length (filter filter_pred (take (unat v'a) daa))"
      and "length ar = unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
      and "daa $ unat v'a \<bind> slookup [Uint 0] = Some yb"
      and "storage_data.vt yb = Address ad"
      and
       "\<forall>y<length daa.
         \<exists>em. daa ! y = storage_data.Array em \<and>
          (\<exists>ad bt. em = [storage_data.Value (Address ad), storage_data.Value (Bytes bt)])"

  shows "length (sdata.ar (the (updateCalldata [Uint v'] (sdata.Value (Uint v'a)) (sdata.Array ar)))) =
          unat (valtype.uint (storage_data.vt (mpa (Address ad))))"
proof -
  from assms(2,6,7,8)
    have "valtype.ad (storage_data.vt (hd (storage_data.ar (daa ! unat v'a)))) = ad"
    by auto
  then have "unat v' < length ar"
    using filter1[where ?P="filter_pred", of "(unat v'a)" daa] assms(2,3,4,5)
    unfolding filter_pred_def by linarith
  then show ?thesis using assms(5) by auto
qed

lemma (in Contract) 7:
  fixes ad
  assumes " \<exists>ar. v' = sdata.Array ar \<and>
            filter_items_prefix (unat x) (storage_data.Array a) ad
             (map (unat \<circ> valtype.uint \<circ> sdata.vt)
               (take (length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat x) a)))
                 ar))"
  shows "\<exists>ar. v' = sdata.Array ar \<and>
            filter_items_prefix (unat (x + 1)) (storage_data.Array a) ad
             (map (unat \<circ> valtype.uint \<circ> sdata.vt)
               (take (length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat x) a)))
                 ar))"
  sorry

lemma (in Contract) 77:
  fixes ad
  shows " length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat x) a)) =
       length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat (x + 1)) a))"
  sorry

lemma (in Contract) 88:
  fixes ad
  shows "length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat x) a)) \<le> unat (x + 1)"
  sorry

lemma (in Contract) 99:
  fixes ad
  shows "unat (v' + 1) = length (filter (\<lambda>x. valtype.ad (storage_data.vt (hd (storage_data.ar x))) = ad) (take (unat (v'a + 1)) daa))"
  sorry

lemma 10:
  fixes ad
  assumes "unat (v'::256 word) \<le> unat v'a"
    and "length daa < 2^256"
    and "unat (v'a::256 word) < length daa"
  shows "unat (v' + 1) \<le> unat (v'a + 1)"
using assms unat_add_lem[where ?'a=256, of v'a 1] unat_add_lem[where ?'a=256, of v' 1] by simp

lemma pred_someE:
  assumes "pred_some P v"
  obtains v' where "v = Some v'" and "P v'"
  using assms unfolding pred_some_def by blast

verification sum_votes:
  myInv
  "K (True)" "K (K (K True))"
  getItems getItems_pre getItems_post
  for "ArrayBuilder"
proof -

  show "\<And>call.
       effect (constructor call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> post s r myInv (K True) (K (K (K True)))"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply wp+
    by (auto simp add: wpsimps)

    show "\<And>call ad.
       effect (getItems call ad) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       getItems_pre ad s \<Longrightarrow>
       inv_state myInv s \<Longrightarrow> post s r myInv (K True) (getItems_post ad)"
    unfolding getItems_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (erule myInvE)
    apply (erule conjE)+
    apply wp+
    defer
    defer
    apply wp+
    defer
    apply wp+
    apply (rule_tac P = "\<lambda>y. \<exists>si. mp y = storage_data.Value (Uint si)" and x = y in allE,assumption)
    apply (rule_tac exE,assumption)
    apply wp+
    apply (rule_tac iv="while_inv y" in wpwhile)
    apply (wp)
    apply (wp)
    apply (wp)
    apply (wp)
    apply (wp)
    apply (wp)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    defer
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    defer
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    defer
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    defer
    apply (safe)[1]
    (*
      3 Goals left
      - whileinv is preserved during execution
      - whileinv implies postcondition
      - whileinv is established
    *)
    defer
    (*Whileinv establishes postcondition*)
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp add: while_inv_def)
    defer
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    defer
    defer
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    defer
    defer
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    defer
    defer
    apply wp
    apply (auto simp add: wpsimps while_inv_def mlookup.simps nth_safe_def xxx split:if_split_asm)[1]
    apply wp
    apply wp
    apply (safe)
    apply (rule while_inv_post,assumption)
    apply (simp add: while_inv_def)
    apply (simp add:mlookup.simps)
    apply (simp add: while_inv_def)[1]
    apply safe
    apply (drule zzz)
    apply (simp)
    apply (simp)
    (*Note: Maybe consider changing the generated intro and elim rules*)
    apply (rule myInvI2)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    (*Whileinv is established*)
    apply (rule while_init)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply mc
    apply (simp add: wpsimps)
    apply (simp add: wpsimps allItems_def getItems_pre_def)
    apply (simp add: wpsimps getItems_pre_def)
    defer
    defer
    apply (simp add: wpsimps)
    defer
    defer
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    defer
    apply (simp add: wpsimps allItems_def getItems_pre_def)
    apply (rule pred_some_copy_memory)
    apply mc+
    apply (simp)
    apply (simp add: wpsimps 2)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply mc
    (*Whileinv is preserved*)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp)
    apply (simp)
    apply (simp)
    defer
    apply (simp)
    apply (simp)
    apply (simp)
    apply wp
    apply wp
    apply wp
    defer
    apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply (simp)
    apply wp
    defer
    apply (auto simp add: wpsimps while_inv_def nth_safe_def split:if_split_asm)[1]
    apply (erule allE)
    back
    apply auto
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    defer
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply wp
    apply wp
    defer
    apply (simp)
    apply wp
    apply wp
    apply wp
    defer
    apply (simp)
    apply wp
    (*2 subgoals: if is true and if is false*)
    defer
    apply wp
    defer
    apply wp
    apply wp
    defer
    (**If condition is false**)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp)
    apply (simp)
    apply (simp)
    defer
    apply (simp)
    apply (simp)
    apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    defer
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    apply (auto simp add: while_inv_def)[1]
    apply wp
    apply wp
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
    apply (rule wp_assign_stack_kdvalue)
    apply (simp)
    apply (simp)
    apply (simp)
    apply (simp)
    apply (simp)
    defer
    apply (simp)
    defer
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (auto simp add: wpsimps while_inv_def allItems_def)[1]
    apply (erule pred_someE)
    apply (rule pred_some_copy_memory,assumption)
    apply (simp add: 7)
    apply (rule 77)
    apply (rule 88)
    (**If condition is true**)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    defer
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply (simp add: while_inv_def)
    apply wp
    apply wp
    apply wp
    defer
    apply (simp)
    apply (simp only:while_inv_def)
    apply safe
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp)
    apply (simp)
    apply (simp)
    defer
    apply (simp)
    apply (simp)
    apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    apply (erule aaaaaa)
    apply (simp)
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
    apply (rule wp_assign_stack_kdvalue)
    apply (simp)
    apply (simp)
    apply (simp)
    apply (simp)
    apply (simp)
    defer
    apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    defer
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply wp
    apply wp
    apply wp
    apply wp
    defer
    apply wp
    apply wp
    apply wp
    apply (erule aaaaaa)
    apply (simp)
    (*Careful: we need to remove the assign_stack rules in Mcalc*)
    apply (rule wp_assign_stack_kdvalue)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    apply (simp add: wpsimps)
    defer
    apply (simp)
    apply wp
    apply wp
    apply wp
    apply wp
    apply wp
    apply (erule pred_someE)
    apply (erule pred_someE)
    apply (auto simp add: wpsimps while_inv_def allItems_def 3 4)[1]
    apply (rule pred_some_copy_memory)
    apply mc+
    apply (simp)
    apply (simp)
    defer
    apply (rule pred_some_copy_memory)
    apply mc+
    apply (simp)
    apply (simp)
    apply (drule zzz1,simp)
    apply (rule updateCalldata_length)
    apply simp
    apply simp
    apply simp
    apply simp
    apply simp
    apply simp
    apply simp
    apply (drule zzz1,simp)
    apply (rule 99)
    apply (drule zzz1,simp)
    apply wp+
    apply (simp add: 10)
    apply (drule zzz1,simp)
    apply (rule filter_items_prefix_suc_eq;simp)
    done
qed
end