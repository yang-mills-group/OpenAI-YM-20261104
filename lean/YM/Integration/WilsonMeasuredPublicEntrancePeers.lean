import YM.Integration.WilsonMeasuredPublicEntrancePorts
import YM.Integration.WilsonThermometerUnitFilingFieldRange
import YM.Integration.WilsonFirstReceivedGalleryRegular

/-! The ordinary part of an actual signed unary return against an arbitrary
finite set of masked original peers. Each native inventory keeps its own
support and threshold and is compared using the common older Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePeers
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Multi QuadraticLocal QuadraticLocal.Earn Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
open WilsonThermometerUnitFilingFieldRange WilsonOriginalAlternativeHearing
open scoped Classical BigOperators
variable {G:Gauge}
theorem lamp {n:Side} {V T I:Type} [DecidableEq V] {J:Census V} {o:V→Site n} {P:Rep G n}
    (E:Lamps T I G P.p o J)(w:V→ℝ)(wp:∀a,0<w a){α C:ℝ}
    (receipt:E.Paid w P.p.B α C)(ap:0≤α)(x:T)(v:V)(U:Config G n):
    ‖(E.log x U).part (J.fire v)‖ ≤ C/w v := by
  apply (le_div_iff₀ (wp v)).mpr
  have bill:=WilsonFirstReceivedGalleryRegular.occupied E receipt ap wp x U (J.fire v) v (by simp [Census.fire])
  simpa only [Poly.toll,Census.fire,prod_singleton,mul_comm] using bill

variable (R:Run G)(d:ℕ){N p t b:ℕ}
local notation "F" => R.family.labels.level d
local notation "sec" => R.family.localSection d
local notation "W" => R.family.path.rep N p t

theorem heard {V:Type} (s:Finset V) (P Q:Rep G (R.family.side t p))
    (sameP:P.eval=(W).eval)(sameQ:Q.eval=(W).eval)(top:t ≤ N)
    (o z:Site (R.family.side t p))(h k:Coefficient F (R.family.side t p))
    {κP κQ M B:ℝ}(hp:h.remBound o P κP M)(kp:k.remBound z Q κQ B)
    (A:V → Config G (R.family.side t p)→ℂ)(fee:V→ℝ)
    (purse:∀v∈s,∀U,‖A v U‖ ≤ fee v)(lower:b ≤ t)(T:Config G (R.family.side b p)):
    ‖held R.family N p
      (fun U=>((soft h).density o sec P U+(soft k).density z sec Q U)*(∏v∈s,A v U)) lower T‖ ≤
      ((cost G d P.p.threshold*(F).coeffSize h.x+M)+(cost G d Q.p.threshold*(F).coeffSize k.x+B))*
        ∏v∈s,fee v :=by
  rw [normalized R.family N p R.makes top _ lower]
  apply actualTransport_norm_le R.family R.makes top _ lower
  intro U
  have unit:((W).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson top U).ne'
  have cp:=point R d P h o hp U
  have cq:=point R d Q k z kp U
  have all:‖∏v∈s,A v U‖ ≤ ∏v∈s,fee v:=by
    rw [norm_prod]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun v hv=>purse v hv U)
  simp only [WilsonPhysicalMarkedDefect.RegularProjection.density,sameP,sameQ,
    Complex.real_smul,Complex.ofReal_inv,←mul_add,←mul_assoc,inv_mul_cancel₀ unit,one_mul]
  rw [norm_mul]
  have sizes:‖h.exponentialEntry o sec P U+k.exponentialEntry z sec Q U‖ ≤ _ :=
    (norm_add_le ..).trans (add_le_add cp cq)
  exact mul_le_mul sizes all (norm_nonneg _) ((norm_nonneg _).trans sizes)

end YM.Integration.WilsonMeasuredPublicEntrancePeers
end
