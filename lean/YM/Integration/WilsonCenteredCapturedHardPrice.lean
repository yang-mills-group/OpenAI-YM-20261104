import YM.Integration.WilsonCenteredCapturedHardFace
import YM.Integration.WilsonCenteredCaptureFares

/-! A genuine native `ForceCost` for the complete crossed hard array
on its original numerical addresses, including the once-divided forcing
allowance and the rooted bill for absorbing the quiet partners. -/
set_option maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredCapturedHardPrice
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Push.Local Planned.GuardedAtom
open WilsonCenteredCapturedHardFace WilsonCenteredCaptureSlots WilsonCenteredCaptureFares
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}
    (D : Lamps X ι G P.p o R) (A : Gallery X μ o P R)
    (w : V → ℝ) (hw : ∀ i, 0<w i) {δ κ v : ℝ}
    (regular : D.Paid w P.p.B (P.p.supportExponent+2) δ)
    (hard : A.K.Paid w P.p.B (P.p.supportExponent+2) κ)
    (quiet : P.activities.KBound P.p v) (left : 0 ≤ v) (room : hitWidth P.p*v ≤ 1)
    (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z) (hk : 0 < κ)
    (K : Guard.Keeper P.p P.activities) (serial : (ι × ℕ) × Finset ℕ ↪ ℕ)

include hw regular hard quiet left room za zb hk

theorem original :
    let bill := 2*Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*δ
    ∃ price : ℕ → ℝ, SumBudget (fun j=>P.p.mass (Push.Local.patch P.activities j) (price j))
      (bill+(hitWidth P.p*v)*bill) ∧ ∀ j, 0 ≤ price j ∧ ∀ x U,
      κ⁻¹*(w a*w b)*‖row D A a b Z K serial x j U‖ ≤ price j := by
  intro bill
  obtain ⟨E,k,posE,read,pk,base,next⟩ := WilsonCenteredCaptureOwnerTariff.original D A w hw regular hard quiet left room a b Z za zb hk
  let T := query D Z
  let c := slot P K T WilsonCenteredCaptureFares.Sel serial
  let amt := fee P T (fun z=>κ⁻¹*E z) k
  let price : ℕ → ℝ := Function.extend c amt 0
  have atKey (q : WilsonCenteredCaptureFares.Tab P T) : price (c q) = amt q := c.injective.extend_apply ..
  have spare (i : ℕ) (un : ¬∃ q,c q=i) : price i = 0 := Function.extend_apply' _ _ _ un
  have home (z : ι × ℕ) : (P.activities.forced z.2).support ⊆ T z := Finset.subset_union_right
  have wallet := WilsonCenteredCaptureFares.roster P T home (fun z=>κ⁻¹*E z) k base next
  refine ⟨price,sumBudget_pass c _ ?_ ?_,?_⟩
  · have same (q : WilsonCenteredCaptureFares.Tab P T) : P.p.mass (Push.Local.patch P.activities (c q)) (price (c q)) =
        P.p.mass (WilsonCenteredOriginalCaptureOwner.ground P (T q.val.1) q.val.2) (amt q) := by
      rw [atKey];exact congrArg (fun S=>P.p.mass S (amt q)) (support P K T WilsonCenteredCaptureFares.Sel serial q)
    simp_rw [same]
    exact wallet
  · intro i hi
    rw [spare i hi]
    exact mul_zero _
  intro i
  by_cases used : ∃ q,c q=i
  · obtain ⟨q,rfl⟩ := used
    rw [atKey]
    have pk' : 0 ≤ ∏ j∈extra P T q,k j := prod_nonneg fun j _=>(pk j).1
    have amtPos : 0 ≤ amt q := mul_nonneg (mul_nonneg (inv_pos.mpr hk).le (posE _)) pk'
    refine ⟨amtPos,?_⟩
    intro x U
    change κ⁻¹ * (w a*w b) * ‖entered P K T WilsonCenteredCaptureFares.Sel serial
      (fun z U=>WilsonCenteredCompulsoryCollection.joint D A a b x U z.1 z.2) (slot P K T WilsonCenteredCaptureFares.Sel serial q) U‖ ≤ amt q
    rw [registered]
    unfold payload
    split
    · rw [norm_mul,norm_prod,←mul_assoc]
      change κ⁻¹ * (w a*w b) * ‖WilsonCenteredCompulsoryCollection.joint D A a b x U q.val.1.1 q.val.1.2‖ *
          (∏ j ∈ extra P T q, ‖(P.activities.K j U : ℂ)‖) ≤ (κ⁻¹*E q.val.1) * ∏ j ∈ extra P T q, k j
      have paid := mul_le_mul_of_nonneg_left (read q.val.1 x U) (inv_pos.mpr hk).le
      rw [←mul_assoc] at paid
      apply mul_le_mul paid _ (prod_nonneg fun _ _=>norm_nonneg _) (mul_nonneg (inv_pos.mpr hk).le (posE _))
      exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>by simpa using (pk j).2 U)
    · simpa using amtPos
  · rw [spare i used]
    refine ⟨le_rfl,?_⟩
    intro x U
    unfold row
    rw [outside P K T owners serial _ i used]
    simp

/-- The same pointwise paid envelope works before any test or sampled field. -/
theorem native (x : X) :
    let bill := 2*Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*δ
    ForceCost P.p P.activities
      (fun j U=> ((κ⁻¹*(w a*w b) : ℝ) : ℂ) * row D A a b Z K serial x j U)
      (bill+(hitWidth P.p*v)*bill) := by
  intro bill
  obtain ⟨p,cost,read⟩ := original D A w hw regular hard quiet left room a b Z za zb hk K serial
  refine ⟨p,cost,fun j=>⟨(read j).1,fun U=>?_⟩⟩
  have sign : 0 ≤ κ⁻¹*(w a*w b) := mul_nonneg (inv_pos.mpr hk).le (mul_nonneg (hw _).le (hw _).le)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg sign]
  exact (read j).2 x U

end YM.Integration.WilsonCenteredCapturedHardPrice
