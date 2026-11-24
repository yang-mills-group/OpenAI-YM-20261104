import YM.RG3.Law.Lamp
import YM.Marker.Weight
/-!
# One-slot forced reader at current construction price

Regrouped K output of d on SAME affected addresses with retained eligibility.
This works also for the canonical reclosure because forced functions retain
complete addresses of origin slot even at zero. Aggregating multiple terms on
common new address is charged per incoming activity label coefficientwise; no
#V cost. The coefficient extraction is suprisingly important because publishing
naturally has many marked alternatives on one vacuum address and canonical
iteration still needs an actual `Coefficient` with all predicates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Law.Emerald
open Marker RG Lattice Wilson Overlay Press Function MeasureTheory RG3.Forms Finset Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable (s : V) (d : Deck R P) {w : V→ℝ} {u c m b a : ℝ}

-- derive explicit K price as well as Borel/local, no hp needed. All K
-- threshold test receipts from d.Active assumed. d.captions etc independent.
omit [Fintype V] in
lemma credit (he : d.Budget w u c m b a) :
    ∃ t : ℕ→ℝ, (∀ i,0≤t i ∧ ∀ U, ‖solution s d i U‖≤t i) ∧
      SumBudget (fun i => P.p.mass (P.activities.forced i).support (t i)) (m*b/(w s)) := by
  let A := d.contents
  obtain ⟨t,ht,H⟩ := he.radial.hits
  let f (j : ℕ×ℕ) := if A.marks j.1 j.2=R.fire s then t j else 0
  let g (i j : ℕ) := if A.marks i j=R.fire s then A.entries i j else 0
  have hv j : 0≤ f j := by unfold f; split <;> first | exact (ht j.1 j.2).1 | exact le_rfl -- syntax bug
  let b0 := m*b/(w s)
  have hx := he.radial.pure s
  let v (x:ℕ) := (P.activities.forced x).support
  have hc : SumBudget (fun j : ℕ×ℕ => P.p.mass (v j.1) (f j)) b0 := by
    unfold b0; rw [div_eq_inv_mul]
    refine budget_mono (budget_scale (x:= (w s)⁻¹) (by positivity) (H s)) (fun j => (hv _).trans (P.p.loMass _ _ (hv _)))
      (fun j => ?_)
    unfold f; dsimp only [A] at *; split
    next H => rw [H,if_pos (show s∈ (R.fire s).val from mem_singleton_self _),Poly.solo_toll,← mul_assoc,inv_mul_cancel₀ hx.ne',one_mul]
    unfold BudgetPoint.mass; rw [mul_zero]
    exact mul_nonneg (by positivity : 0≤(w s)⁻¹) ((H s).1 j)
  have hF := hc.2.1.of_nonneg_of_le hv (fun i => P.p.loMass _ _ (hv i))
  let q i := ∑' j : ℕ,f (i,j)
  have hi i U : ‖solution s d i U‖ ≤ q i := by
    let r j := if A.marks i j=R.fire s then A.entries i j U else 0
    have he j : ‖r j‖ ≤ f (i,j) := by
      unfold r f; dsimp only; split
      · exact (ht i j).2 U
      simp
    have hs : Summable fun j => f (i,j) := hF.comp_injective (Prod.mk_right_injective _)
    have ho := hs.of_nonneg_of_le (fun j => norm_nonneg _) he
    exact (norm_tsum_le_tsum_norm ho).trans (ho.tsum_le_tsum he hs)
  have hn i : 0 ≤ q i := tsum_nonneg (fun j:ℕ => hv (i,j))
  have hs : SumBudget (fun i => ∑' j:ℕ,P.p.mass (v (i,j).1) (f (i,j))) b0 := ⟨fun i => (by refine tsum_nonneg ?_; intro j; exact hc.1 (i,j)),
    ((summable_prod_of_nonneg hc.1).mp hc.2.1).2,hc.2.1.tsum_prod ▸ hc.2.2⟩
  refine ⟨q,fun i => ⟨hn i,hi i⟩,?_⟩
  simpa only [BudgetPoint.mass,tsum_mul_left,q,v] using hs

omit [Fintype V] in
lemma access (h : d.Active) i : Measurable (solution s d i) ∧
    GaugeInvariant (solution s d i) ∧ UsesFinal P.p.threshold (P.activities.forced i).support (solution s d i) ∧
    (∀ U, solution s d i U≠0 → (P.activities.forced i).eligible P.p.threshold U) ∧
    (solution s d i ≠0 → d.contents.origins s∈ (P.activities.forced i).support) := by
  have he := h.articles
  refine ⟨Measurable.tsum (fun j => ?_),fun k U => ?_,fun U W ha hflag => ?_,fun U H => ?_,fun H => ?_⟩
  · change Measurable (fun U => if d.contents.marks i j=R.fire s then d.contents.entries i j U else 0)
    split
    · exact he.meas i j
    exact measurable_const
  · unfold solution; simp_rw [he.invi i _ k U]
  · unfold solution; simp_rw [he.inspects i _ U W ha hflag]
  · by_contra hh; apply H
    unfold solution
    have hi j : d.contents.entries i j U=0 := not_ne_iff.mp fun hu => hh (he.keeps _ _ _ hu)
    simp_rw [hi,ite_self,tsum_zero]
  by_contra c; apply H
  funext U
  unfold solution
  refine (tsum_congr (g:=fun _ => 0) (fun j => ?_)).trans tsum_zero
  split
  next hj => exact congrFun (not_ne_iff.mp (fun hp => c (he.retained i j hp _ (by rw [hj]; exact mem_singleton_self _)))) U
  rfl
end YM.RG3.Law.Emerald
