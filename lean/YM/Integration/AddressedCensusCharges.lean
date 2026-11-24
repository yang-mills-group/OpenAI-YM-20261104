import YM.Integration.SignedCensusActivities
import YM.MergeProof.Stow

/-! Exact per-site invoices for signed regular jet and original physical
hard barcode sums. The original eligibility tests are retained in each
underlying hard atlas entry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.AddressedCensusCharges

open Lattice Wilson RG MergeProof Push.AbsoluteSums
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {I : Type*}

/-- Compress a signed invoice at a common address before taking its
absolute value. The address-dependent loading is carried exactly. -/
theorem grouped (s : ℕ → I) (f : ℕ → ℂ) (u : ℕ → ℝ) (w : I → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hu : ∀ i, ‖f i‖ ≤ u i) {H : ℝ}
    (h : SumBudget (fun i => w (s i)*u i) H) :
    SumBudget (fun a => w a*‖cram s f a‖) H := by
  let g i := w (s i)*u i
  let v i : ℂ := (w (s i):ℂ)*f i
  have hs : HasSum (cram s g) (∑' i, g i) := heavy s h.2.1
  have hg : SumBudget (cram s g) H :=
    ⟨fun a => tsum_nonneg fun i => h.1 i.val,hs.summable,hs.tsum_eq.le.trans h.2.2⟩
  have hv (i : ℕ) : ‖v i‖ ≤ g i := by
    simpa only [v,g,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw (s i))] using
      mul_le_mul_of_nonneg_left (hu i) (hw (s i))
  refine budget_mono hg (fun a => mul_nonneg (hw a) (norm_nonneg _)) ?_
  intro a
  have hh := metric_cram s h.2.1 hv a
  have hc : cram s v a = (w a:ℂ)*cram s f a := by
    unfold cram
    rw [← tsum_mul_left]
    exact tsum_congr fun i => by simp only [v,i.property]
  simpa only [hc,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw a)] using hh

/-- The original signed hard rows grouped by their exact support and
inventory, at their original volume-local cost. -/
theorem forced (A : Activities G n) (p : BudgetPoint) {γ : ℝ} (h : A.KBound p γ)
    (o : Site n) (z : Config G n) :
    SumBudget (fun a : Box n => if o ∈ a.1 then p.mass a.1
      ‖profile A (fun i => Complex.ofReal ∘ A.K i) a z‖ else 0) γ := by
  obtain ⟨u,hu,hE⟩ := h
  let w (a : Box n) := if o ∈ a.1 then Real.exp (p.supportExponent*coverNumber p.B a.1) else 0
  have hw (a : Box n) : 0 ≤ w a := by dsimp only [w]; split <;> positivity
  have hb : SumBudget (fun i => w (barcode A i)*u i) γ := by
    simpa only [barcode,w,ite_mul,zero_mul,BudgetPoint.mass] using hE o
  have hh := grouped (barcode A) (fun i => (A.K i z:ℂ)) u w hw
    (fun i => by simpa only [Complex.norm_real] using (hu i).2 z) hb
  simpa only [profile,Function.comp_apply,w,ite_mul,zero_mul,BudgetPoint.mass] using hh

/-- Every anchored regular derivative on its true healthy mask. The
directions may depend on the original declared site and support. -/
def jet (A : Activities G n) (p : BudgetPoint) (z : Config G n)
    (l : RegularAddress n → List (Directions G n)) (i : ℕ) : ℂ :=
  if Healthy p.threshold (A.reg i).support z
  then Complex.ofReal (leftDerivs (A.E i) (l (A.reg i)) z) else 0

def address (A : Activities G n) (i : ℕ) : Site n × Support n :=
  ((A.reg i).site,(A.reg i).support)

theorem regular (A : Activities G n) (p : BudgetPoint) {H : ℝ} (h : A.EBound p H)
    (o : Site n) (z : Config G n) (l : RegularAddress n → List (Directions G n))
    (hl : ∀ a, (l a).length ≤ p.order)
    (hd : ∀ a, ∀ D ∈ l a, p.dirBound a.site D) :
    SumBudget (fun a : Site n × Support n => if a.1 = o then p.mass a.2
      ‖cram (address A) (jet A p z l) a‖ else 0) H := by
  obtain ⟨u,hu,hE⟩ := h
  let w (a : Site n × Support n) := if a.1 = o then Real.exp (p.supportExponent*coverNumber p.B a.2) else 0
  have hw (a : Site n × Support n) : 0 ≤ w a := by dsimp only [w]; split <;> positivity
  have hb : SumBudget (fun i => w (address A i)*u i) H := by
    simpa only [address,w,ite_mul,zero_mul,BudgetPoint.mass] using hE o
  have hj (i : ℕ) : ‖jet A p z l i‖ ≤ u i := by
    unfold jet
    split
    next hgood => simpa only [Complex.norm_real] using (hu i).2 z hgood _ (hl _) (hd _)
    next => simpa only [norm_zero] using (hu i).1
  simpa only [w,ite_mul,zero_mul,BudgetPoint.mass] using grouped (address A) _ u w hw hj hb

end YM.Integration.AddressedCensusCharges
end
