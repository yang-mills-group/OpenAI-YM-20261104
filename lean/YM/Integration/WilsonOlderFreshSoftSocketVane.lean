import YM.Integration.WilsonMaxwellThermometerStationHeads
import YM.Integration.WilsonInvariantActionCaptureCharge
import YM.Integration.WilsonNeutralOffsetCutoff

/-! The complete physical amount of the original nominated finite source at its own station. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketVane
open Function Filter Finset Wilson RG Source Labels Next.Rank Next.Rank.East Next.Rank.Price Next.Rank.Station
open Next.Rank.Atlas Further.CorrectedLift
open Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerMaximalHead
open scoped Classical BigOperators Topology

variable {G:Gauge}

theorem complete {d:ℕ}(F:Labels.Frame G d)(ρ θ μ ε:ℝ)(x y p:F.Coeff)
    (scale:1≤ρ)(pos:0<θ)(small:θ≤1)(upper:θ⁻¹≤μ)(half:ε≤1/2)
    (eqn:∀i:F.Index,(θ:ℂ)^(F.grades i).2*y i=(ρ:ℂ)^(F.grades i).1*p i)
    (rent:F.coeffSize (x-y)≤ε*F.coeffSize x):
    F.coeffSize x≤2*ρ^d*μ^(d/2)*F.coeffSize p:=by
  have rpos:0<ρ:=zero_lt_one.trans_le scale
  have hθ:1≤θ⁻¹:=(one_le_inv₀ pos).mpr small
  have gross:F.coeffSize y≤ρ^d*μ^(d/2)*F.coeffSize p:=by
    unfold Frame.coeffSize
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro i _
    have mode:=congrArg norm (eqn i)
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,abs_of_pos rpos] at mode
    have localize:‖y i‖=θ⁻¹^(F.grades i).2*(ρ^(F.grades i).1*‖p i‖):=by
      rw [←mode,inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ pos.ne'),one_mul]
    have angular:θ⁻¹^(F.grades i).2≤μ^(d/2):=
      (pow_le_pow_right₀ hθ (rank F i)).trans (pow_le_pow_left₀ (inv_nonneg.mpr pos.le) upper _)
    rw [localize,mul_right_comm (ρ^d),mul_comm (ρ^d*‖p i‖)]
    exact mul_le_mul angular (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ scale (F.bound i)) (norm_nonneg _))
      (mul_nonneg (pow_nonneg rpos.le _) (norm_nonneg _)) (pow_nonneg ((inv_nonneg.mpr pos.le).trans upper) _)
  have tri:F.coeffSize x ≤ F.coeffSize (x-y)+F.coeffSize y:=by
    unfold Frame.coeffSize
    rw [←sum_add_distrib]
    exact sum_le_sum fun i _=>by simpa only [Pi.sub_apply,sub_add_cancel] using (norm_add_le (x i-y i) (y i))
  have xn:0≤F.coeffSize x:=sum_nonneg fun _ _=>norm_nonneg _
  have halfpaid:=rent.trans (mul_le_mul_of_nonneg_right half xn)
  linarith only [tri,halfpaid,gross]

variable (R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "road" => R.family.path.levels

def quotaFare (A:Group C 6)(i:Fin 3):ℝ:=
  let k:=A.station.k
  let j:=index A (grade i)
  2*(Station.gap road A.station.b k)^j.val*(2*(road).clock.monitor k)^(j.val/2)*
    ((C).labels.level j).coeffSize (ladder C j (A.change (grade i) (source C univ i)))

theorem original (simple:G.Simple):∀ᶠk:ℕ in atTop,∀A:Group C 6,A.station.k=k→
    A.station.checked f H A.horizon→∀N per,k<N→∀i,
      Next.UVStress.quota C (grade i) k N per (WilsonNeutralOffsetCutoff.named R A N per i)≤quotaFare R A i:=by
  filter_upwards [WilsonMaxwellThermometerStationHeads.clock R simple,
    (WilsonMaxwellThermometerStationHeads.rate R simple).eventually_lt_const (by norm_num:(0:ℝ)<1/2)] with k issued close
  intro A eqn check N per top i
  subst k
  let k:=A.station.k
  let j:=index A (grade i)
  let w:=A.change (grade i) (source C univ i)
  let p:=ladder C j w
  let v:=A.station.wheel.atCut (N,per) j w
  let ρ:=Station.mag road A.station.b k
  let θ:=shrink C k N per
  have ready:=issued.2.2 N per top.le
  have small:θ≤1:=ready.2.trans ((div_le_one (by linarith only [issued.2.1])).mpr issued.2.1)
  have scale:1≤ρ:=Real.one_le_rpow ((by norm_num:(1:ℝ)≤2).trans issued.2.1)
    (le_of_lt ((by norm_num:(0:ℝ)<5).trans check.high.1))
  obtain ⟨charts,sky⟩:=check.rate N per top
  have solved:Solves C ρ j k N per (A.station.R N per j) p v:=
    poured R.makes (check.early j) top.le ρ _ ((charts j).1) p
  have paid:=complete ((C).labels.level j) ρ θ (2*(road).clock.monitor k)
    (WilsonMaxwellThermometerStationHeads.fee R k) (awake C j k N per v) ((A.station.R N per j) v) p
    scale ready.1 small (shrink_min C R.makes top.le per) close.le
    (fun z=>by simpa only [Solves,Frame.scaled_apply,Complex.ofReal_pow,weightTag,LinearMap.coe_mk,AddHom.coe_mk]
      using congrFun solved z) (sky j v)
  change Spindle.paid C j k N per v ≤ _ at paid
  rw [WilsonInvariantActionCaptureCharge.amount] at paid
  have price:=mul_le_mul_of_nonneg_left paid (pow_nonneg ((C).S.a_pos k).le j.val)
  rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ ((C).S.a_pos k).ne'),one_mul] at price
  calc
    _≤_:=price
    _=quotaFare R A i:=by
      change (C).S.a k^j.val*(2*ρ^j.val*(2*(road).clock.monitor k)^(j.val/2)*_)=
        2*((C).S.a k*ρ)^j.val*(2*(road).clock.monitor k)^(j.val/2)*_
      rw [mul_pow]
      ring

end YM.Integration.WilsonOlderFreshSoftSocketVane
end
