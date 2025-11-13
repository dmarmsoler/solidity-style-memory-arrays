theory Aliasing
  imports Mcalc
begin

(*
  bool[1][1] memory x = [[false]];
  bool[1][1] memory y = [[false]];
  x[0] = y[0];
  y[0][0] = true;
  assert (x[0][0] == true);
*)

lemma (in Contract) example:
  "wp (do {
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''x'');
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad 0] (stackLookup (STR ''y'') [sint_monad 0]);
        assign_stack_monad (STR ''y'') [sint_monad 0,sint_monad 0] (true_monad)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint 0, Uint 0] cd = Some (adata.Value (Bool True))))
      (K (K True))
      s"
  apply wp+
  apply (auto simp add: is_Array_write alookup.simps)
  apply wp+
  apply (auto simp add: pred_memory_def)

  (*Aliasing*)
  apply (drule_tac ?xs1.0 = "[Uint 0]" and ?l1.0=l in aliasing, simp, simp)
  apply (erule mlookup_mupdate, simp)
  apply (erule locations_write, simp add:alookup.simps)
  apply (erule mlookup_locations_write_2, simp add:alookup.simps)
  apply (erule mlookup_some_write, simp add:alookup.simps)
  apply (erule mlookup_loc_write, simp add:alookup.simps)
  apply (erule nth_some, simp)
  apply (rule mlookup_neq_write, assumption, simp)
  apply (erule mlookup_some_write, simp add:alookup.simps)
  apply (erule mlookup_loc_write, simp add:alookup.simps)
  apply (erule mlookup_nth_mupdate, simp)
  apply (erule mlookup_locations_write_3)
  apply (erule mlookup_some_write, simp add:alookup.simps)
  apply (erule locations_write,simp add: alookup.simps)
  apply (erule mlookup_locations_write_1,simp add: alookup.simps)
  (*Aliasing*)

  apply (rule pred_some_read)
  apply (erule read_mupdate_value)
  apply (erule disjoined_mupdate, simp, simp)
  apply (erule locs_locs_write_2)
  apply (erule locs_locs_write_1)
  apply (erule disjoined_locs_write_2)
  apply (erule locs_locs_write_1)
  apply (erule disjoined_locs_write_1)
  apply (erule locs_locs_write_1)
  apply (erule disjoined_locs_write_1)
  apply (erule locs_locs_disj_write)
  apply (erule locs_locs_write_1)
  apply (erule read_mupdate_1, simp, simp)
  apply (erule disjoined_locs_write_2)
  apply (erule locs_locs_write_1)
  apply (erule disjoined_locs_write_1)
  apply (erule locs_locs_disj_write)
  apply (erule locs_locs_write_1)
  apply (erule read_write)
  apply (erule locs_locs_write_1)
  apply (erule write_read, simp add:prefix_def)
  apply (erule write_read, simp add:prefix_def)
  by (simp add:alookup.simps)

lemma (in Contract) example_short:
  "wp (do {
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''x'');
        write (adata.Array [adata.Array [adata.Value (Bool False)]]) (STR ''y'');
        assign_stack_monad (STR ''x'') [sint_monad 0] (stackLookup (STR ''y'') [sint_monad 0]);
        assign_stack_monad (STR ''y'') [sint_monad 0,sint_monad 0] (true_monad)
      })
      (pred_memory (STR ''x'') (\<lambda>cd. alookup [Uint 0, Uint 0] cd = Some (adata.Value (Bool True))))
      (K (K True))
      s"
  apply wp+
  apply (auto simp add: is_Array_write alookup.simps)
  apply wp+
  apply (auto simp add: pred_memory_def)

  (*Aliasing*)
  apply (drule_tac ?xs1.0 = "[Uint 0]" and ?l1.0=l in aliasing, simp, simp)
  apply (mc+, (auto simp add:alookup.simps)[1])+
  apply (rule pred_some_read)
  apply mc+
  by (simp add:alookup.simps)

end