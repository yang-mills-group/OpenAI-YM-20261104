import YM.Integration.WilsonMatrixTicketLanesReflectedFields
import YM.Integration.WilsonMatrixTicketLanesReflectedGauge

/-! All-orders spatial price on the normalized real Wilson roster, after its exact engineering shift. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedRank
open Function Filter Finset Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open RGComparison.Core16.Spool RGComparison.Core16.Silk
open WilsonMatrixTicketLanesDescentWords WilsonMatrixTicketLanesReflectedGauge
open scoped Topology Classical BigOperators
variable {G : Gauge} {I J : Type} [Fintype I] [Fintype J] {c f : Side}
    (S : StepData c f) (T : Forest S.ratio) {P : Oven S.patch} (X : P.Form G) (u : Directions G c)
    (R : Run G) (d : I→ℕ) (h : J→ℕ) (j : ∀i,(R.family.labels.level (d i)).Index)
    (k : ∀i,(R.family.labels.level (h i)).Index) (x : I→Site f) (y : J→Site f)
local notation "A" => lamps R d j
local notation "B" => lamps R h k
local notation "w" => power (pair (lamps R d j) (lamps R h k))
local notation "net" => WilsonMatrixTicketLanesReflectedGauge.gap S T X u R d h j k x y
local notation "raw" => WilsonMatrixTicketLanesReflectedFields.series S T A B x y false false X u
variable (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S) (pin : ∀i,‖u i‖≤X.Q)

private theorem monomial (t : ℕ) : train (fun g : ℝ=>g^t) ((PowerSeries.X : Roll)^t) := by
  convert train.mono t (1:ℝ) using 1
  · simp
  · apply PowerSeries.ext;intro l
    simp [PowerSeries.coeff_monomial,PowerSeries.coeff_X_pow,eq_comm]

include offer large pin

/-- The original physical joint and both original means fix this whole formal identity. -/
theorem original : raw = PowerSeries.X^w*net := by
  have numerical:= (monomial w).produces (physical S T X u R d h j k x y offer large pin)
  have response : train (WilsonMatrixTicketLanesReflectedFields.covariance S T A B x y false false X u) (PowerSeries.X^w*net) := by
    apply numerical.travel
    have valid : ∀ᶠ g : ℝ in PertExtension.Series.Tested.germ,0<g := self_mem_nhdsWithin
    filter_upwards [valid] with g gp
    exact (complete S T X u R d h j k x y large gp).symm
  exact (WilsonMatrixTicketLanesReflectedFields.measured S T A B x y false false X u offer large pin).unique response

/-- Price only actual normalized coefficients, with the true total engineering order spent first. -/
theorem coefficient {q v e : ℕ} (degree : v≤q) {C : ℝ} (hC : 0≤C)
    (prices : Past X C (w+q) (w+q) (w+q))
    (distance : ∀i : Slice A,∀k : Slice B,e≤Lattice.separation (legs A x i).1 (legs B y k).1) :
    |nth v net| ≤ C/costLamp X e*bond_fee (look false ∘ sight A) (look false ∘ sight B) X.Q (w+q) := by
  have hp:=WilsonMatrixTicketLanesReflectedFields.price S T A B x y false false X u offer large pin
    hC prices (Nat.add_le_add_left degree w) distance
  rw [original S T X u R d h j k x y offer large pin] at hp
  change |PowerSeries.coeff (w+v) (PowerSeries.X^w*net)|≤_ at hp
  simpa only [PowerSeries.coeff_X_pow_mul',le_add_iff_nonneg_right,Nat.zero_le,if_true,Nat.add_sub_cancel_left] using hp

end YM.Integration.WilsonMatrixTicketLanesReflectedRank
