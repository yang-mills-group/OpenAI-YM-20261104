import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.IterationFour.Running

/-!
# Exact additions to the regular activity list, with the actual budgets

Render additional vacuum packets on the same torus. No changing support or
attempting to omit or zero any forced label on this branch. In particular,
K hypotheses will still be needed separately. E is in the *negative* exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side}

/-- Aligned payload in the regular negative log. *After* any path completions, mask
    alignment, clover contact, and re-expression required to meet the early local
    bounds. (Those operations need their own proof, especially of flags.) -/
structure Payload (G : Gauge) (n : Side) where
  labels : ℕ → RegularAddress n
  action : ℕ → Config G n → ℝ

namespace Payload
variable (P : Payload G n) (p : BudgetPoint)
structure Invoice (c : ℝ) : Prop where
  smooth i : p.Regular (P.labels i).support (P.action i)
  flat i : P.action i 1 = 0
  null i : Nonwrapping (P.labels i).support (P.labels i).site →
    ∀ x y, IsAffineDirection (P.labels i).site x → IsAffineDirection (P.labels i).site y →
      logHessian (P.action i) x y = 0
  moves : ∀ s b, ∃ π : Equiv.Perm ℕ, ∀ i : ℕ,
    (P.labels (π i)).site=affine s b (P.labels i).site ∧
    (P.labels (π i)).support=(P.labels i).support.image (affine s b) ∧
    ∀ U, P.action (π i) U=P.action i (pull s b U)
  credit : ∃ v : ℕ→ℝ,
    (∀ i, p.supBounds (P.labels i).site (P.labels i).support (P.action i) (v i)) ∧
    ∀ o, SumBudget (fun i=> if (P.labels i).site=o then p.mass (P.labels i).support (v i) else 0) c

/-- Append with a *disjoint address space*. Alignment for the later difference
    means the same P, not the same exponential applied to unaligned labels. -/
def coding := Equiv.natSumNatEquivNat.symm

def attach (k : ℝ) (A : Activities G n) : Activities G n :=
  { A with
    reg := Sum.elim A.reg P.labels ∘ coding
    E := Sum.elim A.E (k • P.action) ∘ coding }

def amount (U : Config G n) := ∑' i, masked p.threshold (P.labels i).support (P.action i) U
variable {P p}

lemma nonneg {c : ℝ} (h : P.Invoice p c) : 0 ≤ c := Extra.Iteration.Cost.nonneg (h.credit.choose_spec.2 0)
lemma payment {a c b : ℝ} (k : ℝ) {A : Activities G n} (h : P.Invoice p c) (ha : A.Valid p a b) :
    (P.attach k A).Valid p (a + ‖k‖*c) b := by
  let L : ℕ ⊕ ℕ → _ := Sum.elim A.reg P.labels
  let E : ℕ ⊕ ℕ → _ := Sum.elim A.E (k • P.action)
  let Q:= P.attach k A
  change Q.Valid p _ _
  have hV (i : ℕ⊕ℕ) : p.Regular (L i).support (E i) ∧ E i 1=0 ∧
      (Nonwrapping (L i).support (L i).site → ∀ x y, IsAffineDirection (L i).site x →
        IsAffineDirection (L i).site y → logHessian (E i) x y=0) := by
    rcases i with j|j
    · exact ⟨ha.regular.smooth j,ha.regular.at_flat j,ha.regular.vanish j⟩
    refine ⟨WilsonStartup.Start.times_reg k (h.smooth j),?_,?_⟩
    · exact (congr_arg (k • ·) (h.flat j)).trans (smul_zero ..)
    intro hl x y hx hy
    let f := AnalyticBridge.VerifiedReset.germ (P.action j)
    change (iteratedFDeriv ℝ 2 (k • f) 0) _ = 0
    rw [iteratedFDeriv_const_smul_apply (AnalyticBridge.VerifiedReset.germ_diff (h.smooth j))]
    exact (congr_arg (k • ·) (h.null j hl x y hx hy)).trans (smul_zero ..)
  refine ⟨⟨fun i=> (hV (coding i)).1, fun i => (hV (coding i)).2.1, fun i=>(hV (coding i)).2.2⟩,
    ⟨ha.forced.sym,ha.forced.symtest,ha.forced.meas,ha.forced.meas_test,ha.forced.reads,ha.forced.reads_test,
      ha.forced.permit⟩, ?_, ?_, ha.boundK⟩
  · intro s b
    obtain ⟨π,hπ⟩ := h.moves s b
    obtain ⟨e⟩ := ha.moves s b
    let u := Equiv.sumCongr e.ep π
    let ζ := (coding.trans u).trans coding.symm
    have hr i : coding (ζ i)=u (coding i) := Equiv.apply_symm_apply ..
    have hp (i:ℕ⊕ℕ) : (L (u i)).site=affine s b (L i).site ∧ (L (u i)).support=(L i).support.image (affine s b) ∧
        ∀ U, E (u i) U=E i (pull s b U) := by
      rcases i with i|i
      · exact ⟨e.reg_site i,e.reg_support i,e.valuesE i⟩
      exact ⟨(hπ i).1,(hπ i).2.1, fun U=> congr_arg (k • ·) ((hπ i).2.2 U)⟩
    refine ⟨⟨ζ,e.kp,fun i=> ?_,fun i=>?_,e.forced_support,e.forced_inventory,e.forced_tests,fun i=>?_,e.valuesK⟩⟩
    · change (L (coding (ζ i))).site=affine s b (L _).site; rw [hr]; exact (hp _).1
    · change (L (coding (ζ i))).support=(L _).support.image _; rw [hr]; exact (hp _).2.1
    intro U; change E (coding (ζ i)) U=E (coding _) _; rw [hr]; exact (hp _).2.2 U
  obtain ⟨u,h1,h2⟩ := h.credit
  obtain ⟨v,hV,hA⟩ := ha.boundE
  let B := Sum.elim v (fun i=>‖k‖*u i)
  refine ⟨B ∘ coding, fun i=>?_,fun o=>?_⟩
  · change p.supBounds (L (coding i)).site (L (coding i)).support (E (coding i)) (B (coding i))
    rcases coding i with j|j
    · exact hV j
    exact WilsonStartup.Start.times_bound k (h1 j)
  let f (i:ℕ⊕ℕ) := if (L i).site=o then p.mass (L i).support (B i) else 0
  have hx : SumBudget f (a + ‖k‖*c) := by
    refine Extra.Iteration.Cost.sum (hA o) ?_
    have hp := YM.Push.AbsoluteSums.budget_scale (norm_nonneg k) (h2 o)
    simpa only [f,B,L,Sum.elim_inr,BudgetPoint.mass,mul_left_comm,mul_ite,mul_zero] using hp
  exact Extra.Iteration.Cost.equiv coding hx

lemma pays_add {a c b : ℝ} (k : ℝ) {A : Activities G n} (h : P.Invoice p c) (ha : A.Valid p a b)
    (U : Config G n) : (P.attach k A).additive p U = A.additive p U + k*P.amount p U := by
  let f (i : ℕ⊕ℕ) := (P.attach k A).regularOccurrence p (coding.symm i) U
  have hs : Summable f := coding.summable_iff.mp (by
    simp only [Function.comp_def, f, Equiv.symm_apply_apply]
    exact (Activities.ESeries (payment k h ha)).summable U)
  -- spelling out reindexing
  have he(i) : (P.attach k A).regularOccurrence p i U=f (coding i) := by simp [f]
  unfold Activities.additive
  conv_lhs => enter [1, i]; rw [he]
  rw [coding.tsum_eq f, Summable.tsum_sum (f:=f) ?_ ?_]
  · congr 1
    · apply tsum_congr; intro i
      simp only [f,Activities.regularOccurrence,attach,Function.comp_apply,Equiv.apply_symm_apply,Sum.elim_inl]
    unfold amount
    rw [← tsum_mul_left]; apply tsum_congr; intro i
    simp only [f,Activities.regularOccurrence,attach,Function.comp_apply, Equiv.apply_symm_apply,
      Sum.elim_inr, Pi.smul_apply]
    by_cases hv : Healthy p.threshold (P.labels i).support U <;> simp [hv]
  · exact hs.comp_injective Sum.inl_injective
  exact hs.comp_injective Sum.inr_injective
lemma unchanged {P : Payload G n} (k : ℝ) (A : Activities G n) (p : BudgetPoint) :
    (P.attach k A).gas p=A.gas p := rfl
end Payload
end YM.IterationFour.Vacuum
