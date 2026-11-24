import YM.Integration.WilsonPositionRawPolynomial

/-! The compact raw array on the independently prescribed auxiliary lattice, before the
continuum limit. Every field slot is changed by the original two finite field matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionRawEpoch
open Filter Set Finset Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries
open WilsonPositionRawFiling WilsonPositionRawMesh
open scoped BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    {i B n : ℕ} (P : Handoff.Directory Z i B) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d)

def matrix (i d : ℕ) : Guard G d :=
  deck (Z.store.layout Z.scheme (Z.run.step i) d) *
    (key Z (Z.run.step i)).gate (Scale.Measure.adjust Z.scheme Z.criterion d)

def row (k : ℕ) : ℂ :=
  ∑ a ∈ tally k n, ∑ t,
    Dframe.each t (pulseU a (matrix Z i d) v) * coeff (a none) (P.sweep_fk n d φ t)

include H in
theorem coefficient (k : ℕ) (cover : Handoff.Directory.budget G n d + k ≤ B) :
    coeff k (said (published Z (Z.run.step i) d) φ v) = row Z P d φ v k := by
  rw [show coeff k (said (published Z (Z.run.step i) d) φ v) =
    published Z (Z.run.step i) d k n φ v from coeff_mk ..]
  unfold published
  rw [← Z.store.fits_walk,parlance,really]
  apply sum_congr rfl
  intro a ha
  have hk : a none ≤ k := ((totaled a).mp ha) ▸ single_le_sum (f:=fun j=>a j)
    (fun _ _ => Nat.zero_le _) (mem_univ none)
  exact (H.batchFromEpochFk i B P d (a none) n (fun _=>0) φ (pulseU a (matrix Z i d) v) (by omega)).2

include H in
theorem through (q : ℕ) (use : Rose.Use Z.scheme Z.criterion (Z.run.step i))
    (cover : Handoff.Directory.budget G n d + q ≤ B) (x : ℝ) :
    raw Z (Z.run.step i) q d φ v x =
      ∑ k ∈ range (q+1), row Z P d φ v k * (x:ℂ)^k := by
  rw [WilsonPositionRawPolynomial.issued Z _ q d φ v use x,PowerSeries.trunc_apply,
    Nat.Ico_zero_eq_range]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply sum_congr rfl
  intro k hk
  rw [coefficient Z H P d φ v k (by have := mem_range.mp hk; omega)]

include H in
/-- One available original directory gives the entire raw compact polynomial at every
argument. Its top degree includes every permitted field-matrix coefficient. -/
theorem booked (i q : ℕ) (use : Rose.Use Z.scheme Z.criterion (Z.run.step i)) :
    ∃ D : Handoff.Directory Z i (Handoff.Directory.budget G n d + q), ∀ x : ℝ,
      raw Z (Z.run.step i) q d φ v x = ∑ k ∈ range (q+1), row Z D d φ v k * (x:ℂ)^k := by
  obtain ⟨D⟩ := H.packets i (Handoff.Directory.budget G n d + q)
  exact ⟨D,through Z H D d φ v q use le_rfl⟩

end YM.Integration.WilsonPositionRawEpoch
