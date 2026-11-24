import YM.Contacts.Procession.Fruit
/-! # Marked ledger estimates for signed linear integral read. -/
noncomputable section
namespace YM.Contacts.Procession.Hinges
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
set_option autoImplicit false
variable {X Y A B ι κ α β: Type}{n m:Side} {k r:ℕ}{b c:ℝ}
variable {p:X→Y}{q:A→B}{a:X}{u:A}
variable {F: Field ι X}{Z:Y→ℝ}{l: Pulse.Range X}{s:Pulse.Range A}{t:X→A→ℝ}

lemma hinge_at (z:ι→X) : hinge p z=p∘z:= rfl
variable [Fintype ι][Fintype κ]
lemma padCost (h:Ripple l s t)(x:ι→X)(y:ι→A): fee s u y≤ t a u* fee l a x*(∏ i:ι,t (x i) (y i)):= by
    have he:= h.cost (fun i:Option ι=>i.elim a x) (fun i:Option ι=>i.elim u y); rw [Fintype.prod_option] at he; simp only [Option.elim_none,Option.elim_some] at he; unfold fee; apply he.trans_eq; ring
variable {G:ι→X→A→ℝ}{x y:ι→ℝ}
def still (G:ι→X→A→ℝ)(F:Field ι X)(v:(ι→X) × (ι→A)):= F v.1*∏ i:ι,G i (v.1 i) (v.2 i)
lemma placed (h:Ripple l s t)(hp:Rest l a F b)(hv:∀ i,Weirs t (G i) (x i) (y i)): SumBudget (fun p:(ι→X)×(ι→A)=> ‖still G F p‖*fee s u p.2) (t a u*(b*(∏ i,y i))) := by
    have ht:0≤ t a u:= zero_le_one.trans (h.one ..); have hx (p:ι→X) := budget_pi (f:=fun i v=> ‖G i (p i) v‖ *t (p i) v) (fun i=> (hv i).rows _)
    refine budget_mono (budget_scale ht (Cost.prod hp hx (Finset.prod_nonneg fun i _=>(hv i).right))) (fun _=>mul_nonneg (norm_nonneg _) (fee_plus _)) ?_
    rintro ⟨p,q⟩; apply (mul_le_mul_of_nonneg_left (padCost h p q) (norm_nonneg _)).trans_eq; unfold still; simp only [norm_mul,norm_prod,prod_mul_distrib]; ring
lemma light_cost (h:Ripple l s t)(hp:Rest l a F b)(hv:∀ i,Weirs t (G i) (x i) (y i)): Rest s u (allAt G F) (t a u*(b*(∏ i,y i))) := budget_join fee_plus (budget_comm (placed (u:=u) h hp hv))
lemma flight_track (h:Ripple l s t)(hp:Rest l a F b)(hv:∀ i,Weirs t (G i) (x i) (y i))(u:A): Summable (still G F) := (budget_mono (placed (u:=u) h hp hv) (fun z=> norm_nonneg (still G F z)) (fun z=> le_mul_of_one_le_right (norm_nonneg _) (fee_one _))).2.1.of_norm
lemma pack_hoist_aux {H:ι→Y→B→ℝ} (h:Ripple l s t)(hp:Rest l a F b)(hv:∀ i, Weirs t (G i) (x i) (y i))(ht:∀ i,Trails p q (G i) (H i))(u:A): packing q (allAt G F)=allAt H (packing p F):= by
    have hu:= flight_track h hp hv u; let P:= still G F; let Q:= still H (packing p F)
    -- Scroll pi indexed by Fin via reindex
    let g:= (Fintype.equivFin ι).symm
    have he (x':ι→X) : Scroll (hinge (ι:=ι) q) (fun a'=>∏ i:ι, G i (x' i) (a' i)) (fun b'=>∏ i:ι,H i (p (x' i)) (b' i)):= by
       let V i:= G (g i) (x' (g i)); let Y i:= H (g i) (p (x' (g i))); have hp i:Summable (V i):=Summable.of_norm ((hv (g i)).rows _|>.2.1.of_nonneg_of_le (fun w=>norm_nonneg (V i w)) (fun w=> le_mul_of_one_le_right (norm_nonneg _) (h.one ..)))
       have hx i:Scroll q (V i) (Y i):= (ht _).row _; have hu:= (Scroll.pi hp hx).across (q:=hinge (ι:=ι) q) (Equiv.arrowCongr g.symm (Equiv.refl A)) (Equiv.arrowCongr g.symm (Equiv.refl B)) (fun i=>rfl); change Scroll _ (fun a':ι→A=>∏ i, G (g i) (x' (g i)) (a' (g i))) (fun b':ι→B=>∏ i, H (g i) (p (x' (g i))) (b' (g i))) at hu
       convert hu using 1; exact funext fun y'=> (Equiv.prod_comp g (fun i=> G i (x' i) (y' i))).symm; exact funext fun y'=> (Equiv.prod_comp g (fun i=> H i (p (x' i)) (y' i))).symm
    have hx:Scroll (Prod.map (hinge (ι:=ι) p) (hinge (ι:=ι) q)) P Q:= Scroll.chain (p:=hinge (ι:=ι) p) (q:=hinge (ι:=ι) q) (f:=F) (g:=packing p F) (k:=fun x' y'=>∏ i:ι, G i (x' i) (y' i)) (t:=fun x' y'=>∏ i:ι,H i (x' i) (y' i)) (fun _=> rfl) he hu
    let f:=Equiv.prodComm (ι→A) (ι→X); let g':=Equiv.prodComm (ι→B) (ι→Y); exact funext fun i=> (((hx.across f g' (q:=Prod.map (hinge (ι:=ι) q) (hinge (ι:=ι) p)) (fun _=> rfl)).collapse_fst (f.summable_iff.mpr hu)) i).symm
lemma fans_fee (w:κ→ι)(e:Surjective w)(x:ι→X): fee l a (x∘w)=fee l a x:= by
   let v:Option κ→Option ι:=Option.map w; have hv:Surjective v:= by
      intro x; cases x; exact ⟨none,rfl⟩; rename_i x; obtain ⟨y,rfl⟩:=e x; exact ⟨some y,rfl⟩
   refine Eq.trans ?_ (l.retrieve _ (fun i:Option ι=>i.elim a x) hv); unfold fee; congr 1; funext i; cases i <;> rfl
lemma reorder_fee (q:ι≃κ)(h:Rest l a F b): Rest l a (reorder q F) b:= budget_map h (fun x:κ→X=> x ∘ q) (fun _ _ H => funext (q.surjective.forall.mpr (fun i=> congr_fun H i))) (fun v=> (by rw [fans_fee q q.surjective]; rfl)) -- fix
lemma reorder_pack (q:ι≃κ)(p:X→Y)(F:Field ι X): packing p (reorder q F)=reorder q (packing p F):= funext fun i=> (Scroll.across (p:=hinge (ι:=ι) p) (f:=F) (g:=packing p F) (fun i=>rfl) (Equiv.arrowCongr q.symm (Equiv.refl X)) (Equiv.arrowCongr q.symm (Equiv.refl Y)) (q:= hinge p) (fun _=>rfl) i).symm
lemma print_fee (h: Rest l a F b): Rest l a (printRun F) b:= by
    let C:=Equiv.Perm ι; let B:= (Fintype.card (Equiv.Perm ι):ℝ); have hi:B≠0:=by unfold B; positivity
    simpa only [B,printRun,norm_inv, Real.norm_natCast,Finset.sum_const,card_univ,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ hi,one_mul] using ((Rest.sum (u:=univ) (fun i (_: i∈ (univ:Finset (Equiv.Perm ι)))=> reorder_fee i h)).smul B⁻¹)
lemma pack_print (h:Rest l a F b)(p:X→Y): packing p (printRun F)=printRun (packing p F):= by unfold printRun; rw [show ∀ r:ℝ,∀ F:Field ι X, packing p (r • F)=r • packing p F from fun r F=> funext fun i=> ((Scroll.scale (f:=F) (p:=hinge p) (g:=packing p F) (fun _=>rfl) r) i).symm, pack_sum p univ (fun i _=>(reorder_fee i h).summ)]; simp_rw [reorder_pack]
end YM.Contacts.Procession.Hinges
