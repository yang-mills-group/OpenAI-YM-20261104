import YM.QuadraticLocal.Earn.Rendering
import YM.Integration.WilsonPhysicalMarkedDefectSupport

/-! Healthy short coefficients of a prescribed marked Wilson graph. The test, the
field and the choice of a root are made after the supported coefficient bills.
All formulas use the original signed row, its original mark and its whole support. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn Ac Corona Push.AbsoluteSums
open Push.GridApprox.Attach
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
    {A : Passport n V} {Γ : Census V}

/-- The signed coefficient prescribed by the short rows before a field is tested. -/
def shortCoefficient (M : ι → Row A Γ G X) (p : BudgetPoint) (g : ℝ) (s : Γ.Mode)
    (x : X) (U : Config G n) : ℂ :=
  ∑' i, if s = (M i).mode ∧ (M i).length ≤ p.B then (M i).nominal g x U else 0

/-- The identical original rows with the regulator applied on their own supports. -/
def shortRead (M : ι → Row A Γ G X) (p : BudgetPoint) (g : ℝ) (s : Γ.Mode)
    (x : X) (U : Config G n) : ℂ :=
  ∑' i, if (M i).length ≤ p.B then ((rendered M p g).frame i x U).part s else 0

/-- Every short occurrence of a specified mark fits within two actual support
balls about that mark, even if other marked origins coincide. -/
theorem short_support (M : ι → Row A Γ G X) (p : BudgetPoint) (i : ι) (v : V)
    (hv : v ∈ (M i).mode.val) (hi : (M i).length ≤ p.B) :
    (M i).ground p ⊆ halo (2*p.B+10) {A.origin v} := by
  have hr := (M i).heard p.B v hv (A.born v)
  have hball := (M i).cleared p.B hi
  apply Support.collar hr (r := p.B+1) (c := (M i).center) _ (by omega)
  intro y hy
  exact (Animals.neighbors_mem ..).1 (hball ▸ hy)

/-- A healthy collar of any occupied root suffices. External flags, including
flags belonging to independently tested forced terms, are unrestricted. -/
theorem healthy_short (M : ι → Row A Γ G X) (p : BudgetPoint) (g : ℝ) (s : Γ.Mode)
    (v : V) (hv : v ∈ s.val) (x : X) (U : Config G n)
    (healthy : Healthy p.threshold (halo (2*p.B+10) {A.origin v}) U) :
    shortRead M p g s x U = shortCoefficient M p g s x U := by
  unfold shortRead shortCoefficient
  apply tsum_congr
  intro i
  by_cases hs : (M i).length ≤ p.B
  · by_cases hm : s = (M i).mode
    · have hr : v ∈ (M i).mode.val := hm ▸ hv
      rw [if_pos hs,if_pos ⟨hm,hs⟩,Lamps.frame,Poly.part_send,
        if_pos (show s = (rendered M p g).mode i from hm)]
      change (if (M i).clear then (M i).nominal g x U else masked p.threshold ((M i).ground p) ((M i).nominal g x) U) = _
      exact Support.local_read _ _ (short_support M p i v hr hs) healthy
    · rw [if_pos hs,if_neg (fun h => hm h.1),Lamps.frame,Poly.part_send,
        if_neg (show s ≠ (rendered M p g).mode i from hm)]
  · rw [if_neg hs,if_neg (fun h => hs h.2)]

/-- One choice of the original supported angular bounds before every mode,
independent test and root. Its exponential cost is summed at that root with
the original mode weight. This includes clear, field-independent rows. -/
theorem short_bills (M : ι → Row A Γ G X) (p : BudgetPoint) (g : ℝ) (w : V → ℝ)
    {σ b : ℝ} (hw : ∀ v, 0 < w v) (paid : (rendered M p g).Paid w p.B σ b) :
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧
      (∀ i x y, y ∈ (M i).ground p → p.supBounds y ((M i).ground p) ((M i).nominal g x) (c i)) ∧
      ∀ (s : Γ.Mode) (v : V), v ∈ s.val → SumBudget (fun i =>
        if s = (M i).mode ∧ (M i).length ≤ p.B then
          Poly.toll w (M i).mode * c i * Real.exp (σ * coverNumber p.B ((M i).ground p)) else 0) b := by
  obtain ⟨c, hc, htest, hroot⟩ := paid.budget
  refine ⟨c, hc, htest, ?_⟩
  intro s v hv
  have bill := Support.selected (fun i => (M i).ground p) p.B (σ:=σ) (b:=b)
    (f:=fun i => Poly.toll w ((rendered M p g).mode i) * c i)
    (fun i => mul_nonneg (Poly.worth hw _).le (hc i)) hroot (A.origin v)
    (fun i => s = (M i).mode ∧ (M i).length ≤ p.B)
    (fun i hi => (M i).heard p.B v (hi.1 ▸ hv) (A.born v))
  convert bill using 1
  funext i
  by_cases h : s = (M i).mode ∧ (M i).length ≤ p.B
  · simp [h,rendered]
  · simp [h]

/-- The same original full supported derivative majorant at exponent σ+δ
pays every one-root long collection at exponent σ before summing the rows.
The displayed gain uses the native cover number of the whole signed row. -/
theorem long_bills (M : ι → Row A Γ G X) (p : BudgetPoint) (g : ℝ) (w : V → ℝ)
    {σ δ b : ℝ} (hw : ∀ v, 0 < w v) (hδ : 0 ≤ δ)
    (paid : (rendered M p g).Paid w p.B (σ+δ) b) :
    ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧
      (∀ i x y, y ∈ (M i).ground p → p.supBounds y ((M i).ground p) ((M i).nominal g x) (c i)) ∧
      ∀ (s : Γ.Mode) (v : V), v ∈ s.val → ∀ k : ℕ, SumBudget (fun i =>
        if s = (M i).mode ∧ k ≤ coverNumber p.B ((M i).ground p) then
          Poly.toll w (M i).mode * c i * Real.exp (σ * coverNumber p.B ((M i).ground p)) else 0)
        (Real.exp (-δ * k) * b) := by
  obtain ⟨c, hc, htest, hroot⟩ := paid.budget
  refine ⟨c, hc, htest, ?_⟩
  intro s v hv k
  have bill := Support.long (fun i => (M i).ground p) p.B (σ:=σ) (b:=b)
    (f:=fun i => Poly.toll w ((rendered M p g).mode i) * c i)
    (fun i => mul_nonneg (Poly.worth hw _).le (hc i)) hδ hroot (A.origin v)
    (fun i => s = (M i).mode ∧ k ≤ coverNumber p.B ((M i).ground p))
    (fun i hi => (M i).heard p.B v (hi.1 ▸ hv) (A.born v)) k (fun _ hi => hi.2)
  convert bill using 1
  funext i
  by_cases h : s = (M i).mode ∧ k ≤ coverNumber p.B ((M i).ground p)
  · simp [h,rendered]
  · simp [h]

end YM.Integration.WilsonPhysicalMarkedDefect


