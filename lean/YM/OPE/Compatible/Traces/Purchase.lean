import YM.OPE.Compatible.Traces.Shaker
/-! Group product relative to input promises. Uniform meeting bill.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot.Lights
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push.GridApprox.Nil
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {G:Gauge} {C:Family G}{A:Allot C}{V I J Z :Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
    [Fintype J][DecidableEq J] [Fintype Z][DecidableEq Z]{P:Ensemble V}
variable {N p i b H l:ℕ}{F:Fibers (I⊕Z) J}{o:I→Track C.path V p} {o':J→Track C.path V p}
    {E:Track C.path V p} {k:I→ℕ}{k' j:J→ℕ}
    (L:Lights A P N p k (i+1) b E o) {S:Lights A P N p k' i b E o'}
variable {a:ℝ}
-- product across all I⊕Z via grouped(1). estimate by alpha^exponents uniformly, horizon H.
lemma bill_stock (h : Issues L l H F S j)(hH:0<H)(hm:C.ref 0 ≤ i)(hB:Bind C P E F o o' i k k' j) (hw:0<a)(hh:a ≤ valve C H b l i)
    (hy:∀ x:J, ¬ F.SingleFiber x → a ≤ Run.Below C.path (sash C i /2) (j x) (k' x)) (hCard:Fintype.card (I⊕Z) ≤ H):
    a^(H+H)* (∏ u,L.bottom u) ≤ ∏ v,S.bottom v:=by
   let w:=Sum.elim L.bottom (1:Z→ℝ); let c(x):=∏ u∈F.contents x, a*w u; have he:a ≤ 1:=hh.trans (min_le_left ..); have hw' (u:I⊕Z) :0 < w u:=by cases u; exact L.bottom_pos _; exact zero_lt_one
   have ht x:0< c x:=prod_pos fun j _=>mul_pos hw (hw' j); have hQ:Fintype.card J ≤ H:=(Fintype.card_le_of_surjective F.bunch F.sectioned.surjective).trans hCard
   have hp:∏ x,c x=a^(Fintype.card (I⊕Z))*∏ u,L.bottom u:=by
      let B: (Ribbon.Bud J).Mode:= ⟨Finset.univ,mem_univ _⟩; change (∏ x∈B.val,c x)=_
      unfold c; rw [← F.prod_plena,show (F.plena B).val=Finset.univ from eq_univ_of_forall (fun i=>(F.reaped B i).2 (mem_univ _)), prod_mul_distrib,prod_const,card_univ,Fintype.prod_sum_type]; simp [w]
   have hx x: a*c x ≤ tender C H b l i F k' j L.bottom x:=by
      unfold tender; split
      next hh' => exact (mul_le_of_le_one_left (ht _|>.le) he).trans (prod_le_prod (fun i _=> (mul_pos hw (hw' i)).le) (fun i _=> mul_le_mul_of_nonneg_right hh (hw' i|>.le)))
      next hh' =>
         let z:= grouped C.path (renal C.path.levels) H l i (Sum.elim (fun u=>L.bottom u / β C (i+1)^b) 1) F x
         have hz: c x ≤ z:=by
            let δ:= license C.path (renal C.path.levels) H l i; let p:= β C (i+1)^b; have hp:p ≥ 1:= one_le_pow₀ (β_one ..|>.le); have he:a*p ≤ δ:=(le_div_iff₀ (zero_lt_one.trans_le hp)).1 (hh.trans (min_le_right ..))
            refine prod_le_prod (fun j _=>(mul_pos hw (hw' _)).le) (fun i _=>?_)
            cases i
            next v he'=>
               change a*L.bottom v ≤ δ*(L.bottom v/p); rw [← mul_div_assoc]; apply (le_div_iff₀ (zero_lt_one.trans_le hp)).2; rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right he (L.bottom_pos _|>.le)
            next v he'=> exact mul_le_mul_of_nonneg_right ((le_mul_of_one_le_right hw.le hp).trans he) zero_le_one
         exact (mul_le_mul (hy x hh') hz (ht _|>.le) (Run.below_fee _ (div_pos (sash_pos ..) zero_lt_two)|>.le)).trans_eq (by unfold Run.Below z; ring)
   calc
     _ ≤ a^Fintype.card J *(∏ x,c x):=by
           rw [hp,pow_add, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (prod_pos (fun _ _=> L.bottom_pos _)|>.le); exact mul_le_mul (pow_le_pow_of_le_one hw.le he hQ) (pow_le_pow_of_le_one hw.le he hCard) (pow_nonneg hw.le _) (pow_nonneg hw.le _)
     _ ≤ ∏ v,S.bottom v:=by rw [← show ∏ x,a*c x = a^Fintype.card J *(∏ x,c x) from (by rw [prod_mul_distrib,prod_const,card_univ])]; exact prod_le_prod (fun i _=> (mul_pos hw (ht _)).le) (fun i _=> (hx i).trans (bill L h hH hm hB L.bottom (fun i=>L.bottom_pos _) le_rfl i))
end YM.OPE.Allot.Lights
