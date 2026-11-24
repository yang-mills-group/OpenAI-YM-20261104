import YM.Integration.WilsonOriginalStarIncomingRead
import YM.Integration.WilsonThermometerSameWalkTester

/-! Restoring one actual physical slot on the occupied passport. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkTrim
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint
open QuadraticLocal.Fusion.Attached MergeProof.Accent WilsonOriginalStarIncoming
open WilsonOriginalDepositedRegular WilsonOriginalDepositedRegularWindow WilsonOriginalDepositedRegularHearing
open WilsonOriginalStarIncomingRead MeasureTheory
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {d:ℕ} {F:Labels.Frame G d} {Y:Hol G} {P:Rep G n}
  {V T I S₀ S₁:Type} [DecidableEq V] {J:Census V} {H:Passport n V}
  (old:Incoming H P T I J) (j:V) (q:Coefficient F n) (shape:q.Format (H.origin j) Y P)
  (tag:T→ℂ) (D:ℕ)

def pointed : Incoming (Passport.point H.origin) P T I J := ⟨old.old,old.hard⟩

def booked : Incoming H P T (I⊕ℕ) J :=
  let onPoint:=enter (pointed old) j q shape tag D
  ⟨onPoint.old,onPoint.hard⟩

variable [Fintype V] (w:V→ℝ) (active:∀v,0<w v) (test:∀x,‖tag x‖≤1) {κ B e h:ℝ}
  (fund:q.remBound (H.origin j) P κ B)
local notation "full" => booked old j q shape tag D
local notation "α" => P.p.supportExponent+1+1

include active test fund in
theorem paid (reg:old.old.Paid w P.p.B α e) (hard:old.hard.Paid w P.p.B P.p.supportExponent h) :
    (full).old.Paid w P.p.B α (e+Real.exp (3*D)*WilsonRetainedMarkedInletRegular.cost P.p*(w j*B)) ∧
    (full).hard.Paid w P.p.B P.p.supportExponent (h+w j*(κ*B)) :=
  WilsonOriginalStarIncoming.funded (pointed old) j q shape tag D w active test fund reg hard

/- The two independent deposited primary arrays retain their actual difference.
The limit at each regulator hears the remaining long row on the original law. -/
include active test fund in
theorem measured (wide:1 ≤ P.p.supportExponent) (M₀:Lamps T S₀ G P.p H.origin J)
    (M₁:Lamps T S₁ G P.p H.origin J) (C:SectionData F) {a₀ a₁:ℝ}
    (p₀:M₀.Paid w P.p.B α a₀) (p₁:M₁.Paid w P.p.B α a₁)
    (reg:old.old.Paid w P.p.B α e) (hard:old.hard.Paid w P.p.B P.p.supportExponent h)
    (x:T) (U:Config G n):
    ((exhibit (pointed (full)) M₁).density x U).part (J.fire j) -
      ((exhibit (pointed old) M₀).density x U).part (J.fire j) -
      tag x*q.density (H.origin j) C P U =
    (P.eval U:ℂ)*(((M₁.log x U).part (J.fire j)-(M₀.log x U).part (J.fire j)) -
      tag x*primary (P:=P) (o:=H.origin) j q C U - tag x*tail P q D U) :=
  WilsonOriginalStarIncomingRead.original (pointed old) j q shape tag D M₀ M₁ C w active test fund
    wide p₀ p₁ reg hard x U

include shape fund in
omit [DecidableEq V] [Fintype V] in
theorem cofactor {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) {U : Ω → Config G n}
    (mU:Measurable U) (A : Ω → ℂ) (integral:Integrable A μ):
    ‖∫z,A z*tail P q D (U z) ∂μ‖ ≤ Real.exp (-P.p.supportExponent*D)*B*∫z,‖A z‖ ∂μ :=
  WilsonOriginalDepositedRegularHearing.heard P q D μ mU A integral shape fund

end YM.Integration.WilsonThermometerSameWalkTrim
end
