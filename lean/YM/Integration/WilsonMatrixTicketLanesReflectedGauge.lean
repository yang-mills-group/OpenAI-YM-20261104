import YM.Integration.WilsonMatrixTicketLanesArticleSource
import YM.Integration.WilsonMatrixTicketLanesRegulatorWick
import YM.RGComparison.Core16.Silk.Wages

/-! Raw and normalized connected coefficients of the original compact gauge-invariant source pair. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedGauge
open Function Filter Finset Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open FVA2 FVA2.Both RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open RGComparison.Core16.Spool RGComparison.Core16.Silk
open WilsonMatrixTicketLanesDescentWords WilsonMatrixTicketLanesNativePrices
open scoped Topology Classical BigOperators
variable {G : Gauge} {I J : Type} [Fintype I] [Fintype J] {c f : Side}
    (S : StepData c f) (T : Forest S.ratio) {P : Oven S.patch} (X : P.Form G) (u : Directions G c)
local notation "O" => Spool.lens (S:=S) u X T
variable (R : Run G) (d : I→ℕ) (h : J→ℕ) (j : ∀i,(R.family.labels.level (d i)).Index)
    (k : ∀i,(R.family.labels.level (h i)).Index) (x : I→Site f) (y : J→Site f)

omit [Fintype J] in
theorem real (U : Config G f) : (((tally (lamps R d j) x U).re):ℂ) = tally (lamps R d j) x U := by
  let a (i : I) := (FVA2.Track.loadStamp (warehouse R) (x i) (j i)).stencil U
  have printed : (↑(∏i,a i):ℂ)=tally (lamps R d j) x U := by
    rw [Complex.ofReal_prod]; exact Finset.prod_congr rfl fun i _=>WilsonMatrixTicketLanesArticleSource.atom R (d i) (j i) (x i) U
  rw [←printed,Complex.ofReal_re]

def pair (A : I→Lamp G) (B : J→Lamp G) : I⊕J→Lamp G := Sum.elim A B

theorem value (A : I→Lamp G) (B : J→Lamp G) (U : Config G f) :
    tally (pair A B) (Sum.elim x y) U = tally A x U*tally B y U := by
  unfold Spool.tally; rw [Fintype.prod_sum_type]; rfl

theorem degree (A : I→Lamp G) (B : J→Lamp G) : power (pair A B)=power A+power B := by
  unfold power; rw [Fintype.sum_sum_type]; rfl

omit [Fintype J] in
theorem raw (A : I→Lamp G) (large : Bid.Larger (G:=G) S) {g : ℝ} (gp : 0<g) :
    (O).expect g (echo S T A x false g) = g^(power A)*(reads A S u x g).re := by
  have eq := Spool.ice (X:=X) (u:=u) A x false large T g
  change (reads A S u x g).re = g⁻¹^(power A)*(O).expect g (echo S T A x false g) at eq
  rw [eq,←mul_assoc,←mul_pow,mul_inv_cancel₀ gp.ne',one_pow,one_mul]

local notation "A" => lamps R d j
local notation "B" => lamps R h k
local notation "AB" => pair (lamps R d j) (lamps R h k)
local notation "o" => Sum.elim x y

def measured (g : ℝ) := (reads AB S u o g).re-(reads A S u x g).re*(reads B S u y g).re

theorem complete (large : Bid.Larger (G:=G) S) {g : ℝ} (gp : 0<g) :
    (O).expect g (fun z=>echo S T A x false g z*echo S T B y false g z) -
      (O).expect g (echo S T A x false g) * (O).expect g (echo S T B y false g) =
    g^(power AB)*measured S u R d h j k x y g := by
  have together : (fun z=>echo S T A x false g z*echo S T B y false g z) = echo S T AB o false g := by
    funext z
    change (tally A x (T.drape z)).re*(tally B y (T.drape z)).re=(tally AB o (T.drape z)).re
    rw [value x y A B,←real R d j x (T.drape z),←real R h k y (T.drape z)]
    simp
  rw [together,raw S T X u o AB large gp,raw S T X u x A large gp,raw S T X u y B large gp,degree,pow_add]
  unfold measured; ring

/-- Complete independent power series of the normalized, finite-period connected observable. -/
def normalized {L : Type} [Fintype L] (lamps' : L→Lamp G) (o' : L→Site f) : Roll :=
  PowerSeries.mk (Spool.rankℝ lamps' S T X R.metals.O u o' false)

def gap : Roll := normalized S T X u R AB o-normalized S T X u R A x*normalized S T X u R B y

theorem physical (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S) (pin : ∀i,‖u i‖≤X.Q) :
    train (measured S u R d h j k x y) (gap S T X u R d h j k x y) := by
  have forecast {L : Type} [Fintype L] (K : L→Lamp G) (z : L→Site f) :
      train (fun g=>(reads K S u z g).re) (normalized S T X u R K z) :=
    train.sand (Spool.forecast (X:=X) K z false offer large pin T R.alloy.B.ratio)
  exact (forecast AB o).deduct ((forecast A x).produces (forecast B y))

end YM.Integration.WilsonMatrixTicketLanesReflectedGauge
