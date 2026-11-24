import YM.Comparison.Density.Convert.Short
import YM.Comparison.Density.Fusing.Alphabet
import YM.Push.ABSOLUTE_SUMS.Array
import YM.Push.ABSOLUTE_SUMS.Animals

/-!
Vacuum tape and matching. We state estimates before uncertain affine or
value resets. All incidences of moved masks are paid, not just at the
new site. No volume factor in transported E cost or in leftover hit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Convert
open Fusing Mirrors Transport RG Lattice Wilson
open Function MeasureTheory Filter Finset Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {n : Side} {G : Gauge}

abbrev Row (n : Side) := ℕ×Site n
abbrev Start (G : Gauge) (n : Side) := ℕ → Short G n

def seq (n : Side) : ℕ ≃ Row n := by
  letI : Denumerable (Row n) := @Denumerable.ofEncodableOfInfinite _ (Encodable.ofCountable _) _
  exact (Denumerable.eqv (Row n)).symm

def sideEntry (L : Start G n) (a : Row n) : RegularAddress n :=
    ⟨a.2,neighborhood (L a.1).D a.2,(neighborhood_iff ..).2 (by rw [separation_self];exact Nat.zero_le _)⟩

def shift (s : Signed) (x : Site n) : Row n≃Row n:=
    Equiv.prodCongr (Equiv.refl _) ((Signed.actEquiv s).toEquiv.trans (Equiv.addRight x))

def earnings (L : Start G n) (R : Activities G n) : Activities G n :=
    ⟨sideEntry L ∘ seq n,R.forced,(fun z=>(L z.1).proceeds z.2) ∘ seq n,R.K⟩

def baseMist (B : BudgetPoint) (L : Start G n) : Pert.Attach.Corrections G n:=
    ⟨(fun p=> neighborhood (2*(L p.1).D) p.2) ∘ seq n,(fun p=> (L p.1).waste B p.2) ∘ seq n⟩

-- center cost. l shells of actual cover PAID here.
def postage (B : BudgetPoint) (a : ℕ) := Real.exp (B.supportExponent * Animals.ballCost a)
-- reattachment spends one reserve out of this eF
structure Cleared (B : BudgetPoint) (K : LinkTube G) (L : Start G n) (c a eF eR : ℝ) : Prop where
  staged i : Short.Staged B K (L i)
  strongE : 0≤eR
  strongH : 0≤eF
  funded : ∃ k : ℕ→ℕ, (∀ i,(L i).D ≤ k i * B.B) ∧
    SumBudget (fun i=> (L i).loadData B K*postage (Markers.later B eR strongE) (k i)) c ∧
    SumBudget (fun i=> (L i).loss* Animals.ballCost (2*(L i).D)*postage (Markers.later B eF strongH) (2*k i)) a

namespace Cleared
variable {B : BudgetPoint} {K : LinkTube G} {c a eF eR : ℝ} {L : Start G n} {R : Activities G n}
variable (h : Cleared B K L c a eF eR)
include h
lemma smoothE : Art (earnings L R) B := fun _=> (Short.measured (h.staged _) _).1

lemma meetsE : (earnings L R).EBound (Markers.later B eR h.strongE) c := by
  obtain ⟨k,hk,hq,he⟩:=h.funded
  let p:= Markers.later B eR h.strongE
  let A (i) := (L i).loadData B K
  refine ⟨(fun x=> A x.1) ∘ seq n,fun i=> ?_,fun x=>?_⟩
  · exact (Short.measured (h.staged _) _).2
  let f (j : Row n) := if j.2=x then p.mass (neighborhood (L j.1).D x) (A j.1) else 0
  have hf i : 0≤ A i:= (Short.measured (h.staged i) x).2.1
  have he i : SumBudget (fun y : Site n=> f (i,y)) (A i*postage p (k i)):= by
    refine budget_finite (fun y=> ?_) ?_
    · unfold f; split
      · exact mul_nonneg (Real.exp_pos _).le (hf i)
      exact le_rfl
    simp only [f,sum_ite_eq',mem_univ, if_true] -- test
    unfold BudgetPoint.mass postage; rw [mul_comm (A i)]
    refine mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ p.exponent_pos.le)) (hf i)
    exact_mod_cast (Corona.cover_mono (neighborhood_mono (x:=x) (hk i)) B.B).trans (Corona.tile x _ B.B B.B_pos)
  have hx:= budget_pull _ (seq n).injective (budget_rows f (fun i=> A i*postage p (k i)) he hq)
  convert hx using 2 with i; let j:=seq n i
  change (if j.2=x then p.mass _ _ else 0)=f j; unfold f; split
  next hy=> change p.mass (neighborhood (L j.1).D j.2) (A j.1)=_; rw [hy]
  rfl

lemma hitE : Ac.Hit (baseMist B L).region B.B ((fun j=> (L j.1).loss) ∘ seq n) (B.supportExponent+eF) a := by
  obtain ⟨k,hk,hq,hf⟩:= h.funded; intro x
  let p:=Markers.later B eF h.strongH
  let f (j : Row n) := if x∈neighborhood (2*(L j.1).D) j.2 then
      p.mass (neighborhood (2*(L j.1).D) j.2) (L j.1).loss else 0
  let d (i) := 2*(L i).D
  have hn i : 0≤ (L i).loss := (norm_nonneg _).trans (Short.charge (h.staged _) x 1)
  have hg j : 0 ≤ f j:= by unfold f; split; exact mul_nonneg (Real.exp_pos _).le (hn _); exact le_rfl
  have he i : SumBudget (fun y=> f (i,y)) ((L i).loss * Animals.ballCost (d i)*postage p (2*k i)) := by
    apply budget_finite (fun y : Site n=> hg (i,y))
    unfold f; dsimp only
    rw [← Finset.sum_filter]
    have hm : (univ.filter fun y=>x∈ neighborhood (d i) y)= Animals.neighbors (d i) x := by
      ext y; simp [neighborhood_iff, Animals.neighbors_mem, separation_comm]
    let Y:= Animals.neighbors (d i) x; let l:= (L i).loss; let P:=postage p (2*k i)
    rw [hm]
    refine le_trans (b:=∑ _y∈ Y,P*l) ?_ ?_
    · refine sum_le_sum fun y _=> mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ p.exponent_pos.le)) (hn i)
      have ht : d i ≤ (2*k i)*B.B := by unfold d; rw [mul_assoc]; gcongr; exact hk i 
      exact_mod_cast (Corona.cover_mono (neighborhood_mono (x:=y) ht) B.B).trans (Corona.tile y _ B.B B.B_pos)
    rw [sum_const,nsmul_eq_mul]; change (Y.card:ℝ)*(P*l)≤ l*_*P; refine (mul_le_mul_of_nonneg_right (show (Y.card:ℝ)≤ (Animals.ballCost (d i):ℝ) by exact_mod_cast Animals.neighbors_card (d i) x) (show 0≤P*l from mul_nonneg (Real.exp_pos _).le (hn i))).trans_eq (by ring)
  have hx := budget_pull _ (seq n).injective (budget_rows f (fun i=> _) he hf)
  convert hx using 2 with i; let j:= seq n i
  change (if x∈neighborhood (2*(L j.1).D) j.2 then _ else 0)=f j; unfold f; split_ifs
  · unfold BudgetPoint.mass; rw [mul_comm]; rfl
  rfl

def moved {s x} (hp : R.Moves s x) : (earnings L R).Moves s x:= by
  let q : Equiv.Perm ℕ := ((seq n).trans (shift s x)).trans (seq n).symm
  have he i : seq n (q i)= ((seq n i).1,affine s x (seq n i).2):= by simp only [q,Equiv.trans_apply,Equiv.apply_symm_apply]; rfl
  refine ⟨q,hp.kp,fun i=>?_,fun i=>?_,hp.forced_support,hp.forced_inventory,hp.forced_tests,fun i U=> ?_,hp.valuesK⟩
  · dsimp only [earnings,Function.comp_apply,sideEntry]; rw [he]
  · dsimp only [earnings,Function.comp_apply,sideEntry]; rw [he,neighborhood_signed]
  dsimp only [earnings,Function.comp_apply]; rw [he]; exact Short.proceeds_s (h.staged _) _ _ _ U

lemma ready : Pert.Attach.Prepared B.threshold (baseMist B L):= by
  refine ⟨fun i U hi=> Short.wasted_bad (h.staged _) _ _ hi,fun i=>?_,fun i=>?_,fun i=>?_,fun s x=> ?_⟩
  · exact Short.waste_gauge (h.staged _) _
  · exact Short.waste_meas (h.staged _) _
  · exact Short.fits (h.staged _) _
  let q : Equiv.Perm ℕ:= ((seq n).trans (shift s x)).trans (seq n).symm
  have he i : seq n (q i)= ((seq n i).1,affine s x (seq n i).2) := by simp only [q,Equiv.trans_apply,Equiv.apply_symm_apply]; rfl
  exact ⟨q,fun i=> by dsimp only [baseMist,Function.comp_apply]; rw [he, neighborhood_signed],
    fun i U=>by dsimp only [baseMist,Function.comp_apply]; rw [he]; exact Short.waste_orients (h.staged _) _ _ _ U⟩
lemma flag_series (U : Config G n) : Summable fun i => (baseMist B L).value i U:= by
  have he: Ac.Hit _ _ _ ((Markers.later B eF h.strongH).supportExponent) _ := h.hitE
  let M:= baseMist B L; let p:=Markers.later B eF h.strongH
  let f:= (fun j=> (L j.1).loss) ∘ seq n
  have hv i : ‖M.value i U‖ ≤ f i:= Short.charge (h.staged _) _ _
  have ht i : 0 ≤ f i := (norm_nonneg _).trans (hv i)
  have hs i : (M.region i).Nonempty:= ⟨(seq n i).2, (neighborhood_iff ..).2 (by rw [separation_self]; exact Nat.zero_le _)⟩
  apply Summable.of_norm; apply Summable.of_nonneg_of_le (f:=f) (fun i=>norm_nonneg _) hv
  refine Activities.summable_charge (a:=M.region) hs ht (p:=p) (w:=a) fun x=> ?_
  convert he x using 2 with i; unfold BudgetPoint.mass; split_ifs; exact mul_comm ..; rfl

lemma E_series (U : Config G n) : Summable fun i=> (earnings L R).regularOccurrence B i U := by
  let p:= Markers.later B eR h.strongE
  let A:= earnings L R
  obtain ⟨b,hb,hc⟩:= Activities.E_total (A:=A) h.meetsE
  apply Summable.of_norm
  refine hb.of_nonneg_of_le (fun i=> norm_nonneg _) fun i=> ?_
  change ‖RG.masked p.threshold (A.reg i).support _ U‖ ≤ _; by_cases he: Healthy p.threshold (A.reg i).support U
  · rw [masked_eq _ _ _ _ he]; exact (hc _).2 _ he [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact (hc _).1

private lemma almost (U : Config G n) : HasSum (fun i : ℕ=> -(∑ x,(L i).comes x U)) ((∑' i, (baseMist B L).value i U)-(earnings L R).additive B U):= by
  let M:= baseMist B L; let z:= (earnings L R).additive B U
  let f:= fun j : Row n=> (L j.1).waste B j.2 U-(L j.1).gained B j.2 U
  have hs : HasSum f ((∑' i,(baseMist B L).value i U)-z) := (seq n).hasSum_iff.mp (show HasSum _ _ from HasSum.sub ((flag_series h U).hasSum) ((E_series h (R:=R) U).hasSum))
  have he i : HasSum (fun x:Site n=> f (i,x)) (-∑ x,(L i).comes x U) := by
    have he:= Short.balance B (L i) U
    rw [← he,← Finset.sum_sub_distrib]; exact hasSum_fintype _
  exact HasSum.prod_fiberwise hs he

lemma given_paid (U : Config G n) : Summable (fun i : ℕ=> ∑ x,(L i).comes x U) ∧
    (∑' i, (baseMist B L).value i U)=(earnings L R).additive B U-∑' i,∑ x,(L i).comes x U := by
  have hs := almost h (R:=R) U; have he := hs.tsum_eq
  rw [tsum_neg] at he
  refine ⟨?_,by linarith⟩
  simpa using hs.summable.neg
end Cleared
end YM.Comparison.Density.Convert
