import YM.Integration.WilsonMeasuredCompanionFace
import YM.Integration.WilsonThermometerUnitFilingFieldRange
import YM.Integration.WilsonFullFaceSignedUnit

/-! The original measured primary and regular part of the charged column,
with both ordinary spectator groups, under the full older Wilson kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionSoft
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Multi QuadraticLocal QuadraticLocal.Earn Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonThermometerUnitFilingFieldRange WilsonMeasuredCompanionFace
open private ordinary from YM.Integration.WilsonFullFaceSignedUnit
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}{n:Side}{T ι:Type}{o:Fin 3→Site n}{W:Rep G n}
def expense (C:ℝ):ℝ:=Fintype.card (J).Mode * ((Fintype.card (parts (J)).Mode:ℝ)*C^3)

theorem gross (E:Lamps T ι G W.p o (J))(w:Fin 3→ℝ)(positive:∀j,0<w j)
    {α C:ℝ}(cover:E.Paid w W.p.B α C)(ap:0≤α)(cp:1≤C)(v:Fin 3)(s:(J).Mode)(x:T)(U:Config G n):
    ‖peers E v s x U‖ ≤ expense C*w v / Poly.toll w s:=by
  have each (a:(J).Mode):Poly.toll w a*‖(Poly.pass (E.log x U)).part a‖≤
      (Fintype.card (parts (J)).Mode:ℝ)*C^3:=by
    apply ordinary w positive a _ (E.quiet_of_hasSum x U (cover.sums ap positive x U)) cp
    rintro t
    obtain ⟨i,hi⟩:=t.property
    exact WilsonFirstReceivedGalleryRegular.occupied E cover ap positive x U _ i hi
  have full:Poly.price w (Poly.pass (E.log x U))≤expense C:=by
    exact (sum_le_sum (fun i _=>each i)).trans_eq (by simp [expense])
  have amount:=Poly.multiplication positive (Poly.pass (E.log x U)) (Poly.send ((J).fire v) 1)
  rw [Poly.solo,Poly.toll,Census.fire,prod_singleton,norm_one,mul_one] at amount
  apply (le_div_iff₀ (Poly.worth positive s)).mpr
  rw [mul_comm]
  exact (Poly.member positive s _).trans (amount.trans (mul_le_mul_of_nonneg_right full (positive v).le))

variable (R:Run G)(d:ℕ){N per t:ℕ}
local notation "F" => R.family.labels.level d
local notation "S" => R.family.localSection d
local notation "W" => R.family.path.rep N per t

theorem heard {P:Rep G (R.family.side t per)}(same:P.eval=(W).eval)(age:t≤N)
    {o:Fin 3→Site (R.family.side t per)}(v:Fin 3)(h:Coefficient (F) (R.family.side t per))
    {κ M:ℝ}(paid:h.remBound (o v) P κ M)(E:Lamps T ι G P.p o (J))(w:Fin 3→ℝ)(positive:∀j,0<w j)
    {α C:ℝ}(cover:E.Paid w P.p.B α C)(ap:0≤α)(cp:1≤C)(s:(J).Mode)(x:T)(j:ℕ)(jt:j≤t):
    ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (fun U=>(soft h).density (o v) (S) P U*peers E v s x U) j jt‖≤
       (cost G d P.p.threshold*(F).coeffSize h.x+M)*(expense C*w v/Poly.toll w s):=by
  let f:=fun U=>h.exponentialEntry (o v) (S) P U*peers E v s x U
  have source:(fun U=>(soft h).density (o v) (S) P U*peers E v s x U)=
      fun U=>((W).eval U:ℂ)*f U:=by
    funext U
    rw [WilsonPhysicalMarkedDefect.RegularProjection.density,same,mul_assoc]
  rw [source,WilsonThermometerUnitFilingPosterior.weighted]
  apply actualTransport_norm_le R.family R.makes age _ jt
  intro U
  change ‖h.exponentialEntry (o v) (S) P U*peers E v s x U‖≤_
  rw [norm_mul]
  exact mul_le_mul (point R d P h (o v) paid U) (gross E w positive cover ap cp v s x U) (norm_nonneg _)
    ((norm_nonneg _).trans (point R d P h (o v) paid U))

end YM.Integration.WilsonMeasuredCompanionSoft
