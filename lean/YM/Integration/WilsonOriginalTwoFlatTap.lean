import YM.Integration.WilsonOriginalTwoFlatRegular
import YM.Integration.WilsonMeasuredOwnerIntegrable
import YM.Integration.WilsonOriginalFlatOccupiedRate

/-! Once the roots have a common housing, an amplified gallery has a
bounded complete ordinary reading at every older flat on the original law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatTap
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonThermometerUnitFilingCoarse (reading)
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors
open AnalyticBridge.SectorAffine.Offset
open Extra.Histories Multi WilsonCenteredCompleteGallery
open WilsonOriginalFlatOccupiedRate (bill)
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m  ≤  u)(ub:u  ≤  b)
   (fixed:WilsonSingleHardRadius.first R simple  ≤  u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "v₀" => R.alloy.B.a.clock.forcedAllowance b
local notation "Space" => Config G (R.family.side b per)


include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(small:κ ≤ 1)
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    (o:V→Site (R.family.side b per))(G₀:Gallery X ι o (Ψ b) J)(x:X)(s:J.Mode)
    (Z:Support (R.family.side b per))(y:Site (R.family.side b per))(center:y∈Z)
    (resident:∀a∈s.val,o a∈Z)(w:V→ℝ)(radii:∀a,0<w a)
    (regular:G₀.E.Paid w (Ψ b).p.B (Ψ b).p.supportExponent 1)
    (wide:G₀.E.Paid w (Ψ b).p.B ((Ψ b).p.supportExponent+2) 1)
    (hard:G₀.K.Paid w (Ψ b).p.B (Ψ b).p.supportExponent κ)
    {i:ℕ}(ui:u ≤ i)(ib:i ≤ b):
    Poly.toll w s*‖reading R (N:=N) (fun U=>(G₀.density x U).part s) i ib‖ ≤
      (shards J s).card+4*(Poly.toll w s+bill (Ψ b).p Z 1 s.val.card)*β*κ:=by
  let amount:=Poly.toll w s
  let B:=bill (Ψ b).p Z 1 s.val.card
  let H:Space→ℂ:=fun U=>(G₀.density x U).part s-((Ψ b).eval U:ℂ)*soft G₀ x s U
  let Y:Space→ℂ:=fun U=>((Ψ b).eval U:ℂ)*soft G₀ x s U
  have ap:0<amount:=Poly.worth radii s
  have B0:0≤B:=by unfold B WilsonOriginalFlatOccupiedRate.bill WilsonOriginalFlatOccupiedRate.roof;positivity
  have cp:0<1+B/amount:=add_pos_of_pos_of_nonneg one_pos (div_nonneg B0 ap.le)
  have walk:=course.1.walk b (floor.trans ub) cut.le
  have same:(Ψ b).eval=(R.family.path.rep N per b).eval:=walk.view
  obtain ⟨keeper⟩:=WilsonCenteredCourseKeeper.original R course b (floor.trans ub) cut
  obtain ⟨div,hv,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec b capture
  rw [←walk.truep.point] at room
  have paid:=WilsonOriginalFlatOccupiedRate.earned (Ψ b).p Z w radii s (le_refl _) zero_le_one div small room
  have cash:WilsonFullFaceSignedHard.fee (Ψ b).p Z w s 1 κ v₀ κ ≤ 1+B/amount:=
    ((le_div_iff₀ ap).mpr ((mul_comm ..).trans_le paid)).trans (le_add_of_nonneg_left zero_le_one)
  obtain ⟨q,fit,rem,field⟩:=WilsonOriginalFlatOccupiedFace.owned (F:=F) G₀ x s A Z y center resident
    keeper w radii walk.truep.valid hv room div wide hard
  have hardCap:=WilsonMeasuredOwnerFlatCourse.original R π Γ Ψ course cut.le S A y q fit rem simple
    way D Q ticket floor ub fixed cp cash ui ib
  simp only [field] at hardCap
  have hardIncome:Integrable H (prior G _) :=by
    have eq:account q (Ψ b)=H:=funext field
    rw [←eq]
    exact WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course (floor.trans ub) cut.le S A y q fit rem
  have env:Envelope (Ψ b).eval:=(Ψ b).envelope walk.truep.valid
  have gross (U:Space):‖soft G₀ x s U‖ ≤ ((shards J s).card:ℝ)/amount:=
    (le_div_iff₀ ap).mpr ((mul_comm ..).trans_le (WilsonOriginalTwoFlatRegular.masked (Ψ b) G₀.E radii regular x s U))
  have inc:Integrable Y (prior G _):=by
    apply ((env.integrable (prior G _)).norm.mul_const (((shards J s).card:ℝ)/amount)).mono'
      ((Complex.continuous_ofReal.measurable.comp env.1).mul (WilsonOriginalTwoFlatRegular.measurable G₀.E x s)).aestronglyMeasurable
    apply ae_of_all
    intro U
    change ‖((Ψ b).eval U:ℂ)*soft G₀ x s U‖ ≤ ‖(Ψ b).eval U‖*_
    rw [norm_mul,Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (gross U) (norm_nonneg _)
  have combined:(fun U=>(G₀.density x U).part s)=Y+H:=by
    funext U;dsimp only [Y,H,Pi.add_apply];ring
  have softRead:reading R (N:=N) Y i ib=actualTransport R.family (N:=N) (soft G₀ x s) ib 1:=by
    dsimp only [Y];rw [same];exact WilsonThermometerUnitFilingPosterior.weighted R (soft G₀ x s) ib
  have softCap:=WilsonOriginalTwoFlatRegular.older R ib cut.le (Ψ b) G₀.E radii regular x s
  rw [combined,WilsonThermometerUnitFilingRaw.add R Y H inc hardIncome ib,softRead,
    WilsonThermometerUnitFilingRaw.ratio R cut.le (Ψ b) same H ib]
  calc
    _ ≤ amount*‖actualTransport R.family (N:=N) (soft G₀ x s) ib 1‖+
          amount*‖actualTransport R.family (N:=N) (fun U=>((Ψ b).eval U)⁻¹ • H U) ib 1‖:=by
            rw [←mul_add];exact mul_le_mul_of_nonneg_left (norm_add_le ..) ap.le
    _ ≤ (shards J s).card+amount*(4*(1+B/amount)*β*κ):=
      add_le_add softCap (mul_le_mul_of_nonneg_left hardCap ap.le)
    _ = _ := by change _=(shards J s).card+4*(amount+B)*β*κ;field_simp

end YM.Integration.WilsonOriginalTwoFlatTap
end
