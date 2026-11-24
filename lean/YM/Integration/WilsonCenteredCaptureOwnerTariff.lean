import YM.Integration.WilsonCenteredHardEnvelope
import YM.Push.LOCAL_SPLITTING.Funding

/-! A single paid hard alternative already carries its forced divisor.
Adding any eligible quiet owners touching its query costs the local
quiet KBound and two units of the original support exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureOwnerTariff
open Finset Lattice RG Wilson Marker QuadraticLocal Ac Push.Local
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n}

theorem collection {ι : Type*} (T : ι → Support n) (e : ι → ℝ) {v bill : ℝ}
    (quiet : P.activities.KBound P.p v) (left : 0 ≤ v) (room : hitWidth P.p * v ≤ 1)
    (pos : ∀ i, 0 ≤ e i) (old : SumBudget (fun i => reservedMass P.p (T i) (e i)) bill) :
    ∃ k : ℕ → ℝ, (∀ j, 0 ≤ k j ∧ ∀ U, ‖P.activities.K j U‖ ≤ k j) ∧
      SumBudget (fun i => P.p.mass (T i) (e i)) bill ∧
      SumBudget (fun s : (i : ι) × Pack P.activities (T i) =>
        P.p.mass (T s.1 ∪ s.2.val.biUnion (Push.Local.patch P.activities))
          (e s.1 * ∏ j ∈ s.2.val, k j)) ((hitWidth P.p*v)*bill) := by
  obtain ⟨k,proper,rooted⟩ := quiet
  have scale : 0 ≤ hitWidth P.p*v := mul_nonneg (zero_le_one.trans (width_one_le _)) left
  refine ⟨k,proper,sumBudget_mono old (fun _ => mul_nonneg (Real.exp_pos _).le (pos _)) (fun i => ?_) le_rfl,?_⟩
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (by linarith : P.p.supportExponent ≤ P.p.supportExponent+2)
        (Nat.cast_nonneg _))) (pos i)
  · have fees : SumBudget (fun i => mergePrice P.p v (T i) (e i)) ((hitWidth P.p*v)*bill) :=
      sumBudget_mono (sumBudget_mul_left old scale) (fun i => mergePrice_nonneg _ _ left (pos i))
        (fun i => price_meeting left room (pos i) (T i)) le_rfl
    exact sumBudget_sigma (fun i => packBudget (A:=P.activities) (B:=P.p) (T i) (pos i)
        (fun j => (proper j).1) rooted) fees

variable {V X ι μ : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
    (D : Lamps X ι G P.p o R) (A : Gallery X μ o P R)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {δ κ v : ℝ}
    (regular : D.Paid w P.p.B (P.p.supportExponent+2) δ)
    (marked : A.K.Paid w P.p.B (P.p.supportExponent+2) κ)

include hw regular marked

/-- Both surviving sorts of actual configurations have a single divided
invoice. The second sum includes every optional spent quiet support, also
when its nonempty flag lies outside the centered query. -/
theorem original (quiet : P.activities.KBound P.p v) (left : 0 ≤ v) (room : hitWidth P.p*v ≤ 1)
    (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z) (hk : 0 < κ) :
    let native (z : ι × ℕ) := D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support
    let bill := 2*Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*δ
    ∃ (E : ι × ℕ → ℝ) (k : ℕ → ℝ), (∀ z, 0 ≤ E z) ∧
      (∀ z x U, w a*w b*‖WilsonCenteredCompulsoryCollection.joint D A a b x U z.1 z.2‖ ≤ E z) ∧
      (∀ i, 0 ≤ k i ∧ ∀ U, ‖P.activities.K i U‖ ≤ k i) ∧
      SumBudget (fun z => P.p.mass (native z) (κ⁻¹ * E z)) bill ∧
      SumBudget (fun s : (z : ι × ℕ) × Pack P.activities (native z) =>
        P.p.mass (native s.1 ∪ s.2.val.biUnion (Push.Local.patch P.activities))
          ((κ⁻¹ * E s.1) * ∏ j ∈ s.2.val, k j)) ((hitWidth P.p*v)*bill) := by
  intro native bill
  obtain ⟨E,positive,paid,head⟩ := WilsonCenteredHardEnvelope.original D A w hw
    (by linarith [P.p.exponent_pos]) regular marked a b Z za zb hk
  have reserved : SumBudget (fun z => reservedMass P.p (native z) (κ⁻¹ * E z)) bill := by
    convert head using 1
    ext z
    dsimp [reservedMass,native]
    ring
  obtain ⟨k,hk',base,extra⟩ := collection native (fun z => κ⁻¹ * E z) quiet left room
    (fun z => mul_nonneg (inv_pos.mpr hk).le (positive z)) reserved
  exact ⟨E,k,positive,fun z x U=>paid x U z,hk',base,extra⟩

end YM.Integration.WilsonCenteredCaptureOwnerTariff
