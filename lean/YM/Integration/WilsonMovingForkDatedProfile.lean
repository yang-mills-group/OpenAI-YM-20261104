import YM.Integration.WilsonMovingForkDatedExterior
import YM.Integration.WilsonMovingForkShiftedSite

/-! A single bounded exterior can be retained for every real node and smooth
profile on the original selected extraction. The dated inputs themselves are
uniform before the original UV and period limits. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.WilsonMovingForkDatedProfile
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonMovingForkHeterogeneousCut (Invoice Filed Heard)
open WilsonMovingForkMixedSeed (doses product)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonPublicForkTrialHearing
open scoped Classical Topology BigOperators
open WilsonMovingForkDatedExterior (At)
open WilsonMovingForkShiftedSite (Reached)

/-- The same compact numerical exterior for the finite cuts has a common
limit along the already purchased filter. Select it before every position or test. -/
theorem exterior {f:Extraction.Order}{l:Ultrafilter (ℕ×ℕ)}(order:(l:Filter _)≤f.fuse)
    {I:Type}[Fintype I](coeff:(ℕ×ℕ) → I → ℂ)(home:ℝ)
    (budget:f.late fun N per=>∑i,‖coeff (N,per) i‖≤home):
    ∃d:I → ℂ,(∑i,‖d i‖)≤home ∧ Tendsto coeff (l:Filter _) (𝓝 d):=by
  have wage:∀ᶠz:ℕ×ℕ in (l:Filter _),∑i,‖coeff z i‖≤home:=
    ((f.fused _).mpr budget).filter_mono order
  have bounded(i:I):∀ᶠz:ℕ×ℕ in (l:Filter _),coeff z i∈Metric.closedBall (0:ℂ) home:=
    wage.mono fun z fee=>by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (Finset.single_le_sum (f:=fun a=>‖coeff z a‖) (fun _ _=>norm_nonneg _) (mem_univ i)).trans fee
  choose d _ reached using fun i=>(isCompact_closedBall (0:ℂ) home).ultrafilter_le_nhds
    (l.map (fun z=>coeff z i)) (le_principal_iff.mpr (bounded i))
  have land(i):Tendsto (fun z=>coeff z i) (l:Filter _) (𝓝 (d i)):=reached i
  refine ⟨d,le_of_tendsto (tendsto_finsetSum _ fun i _=>(land i).norm) wage,tendsto_pi_nhds.mpr land⟩

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{j n u v c K:ℕ}{d:Fin n→ℕ}{x:∀i,S.Field (d i)}
    (file:Filed R d K)(arms:∀i,Arm R.family S (l:Filter _) (d i) (x i))
    (jK:j≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K)
local notation "C" => R.family

include F in
/-- The physical return is at the original unconditioned coordinate. The
finite report and all later kernel steps use the genuinely translated pins. -/
theorem original (order:(l:Filter _)≤f.fuse)(actual offered:Fin n → Cover)
    (generic:tag ((C).S.a j) actual∈generic n)
    {I:Type}[Fintype I](coeff:(ℕ×ℕ) → I → ℂ)(held pivot:I → ℂ)
    (limit:Tendsto coeff (l:Filter _) (𝓝 held))(column:(ℕ×ℕ) → ℂ)(phase rem:ℝ)(w:Invoice)
    (placed:Reached (R:=R) arms jK uv vc ck actual offered phase)
    (paid:∀ᶠz:ℕ×ℕ in f.fuse,∀top:K<z.1,
      At file uv vc ck jK offered z top (fun i=>(arms i).source z) (column z) w ∧
      ‖column z-∑i,coeff z i*pivot i‖≤rem):
    ‖S.classMoment S d (tag ((C).S.a j) actual) x-∑i,held i*pivot i‖≤phase+w.total v c K+rem:=by
  have physical:=WilsonReflectedPublicAlignedPoints.aligned F order j actual generic (generic_conf n generic) arms
  have expansion:Tendsto (fun z=>∑i,coeff z i*pivot i) (l:Filter _) (𝓝 (∑i,held i*pivot i)):=
    tendsto_finsetSum _ fun i _=>((tendsto_pi_nhds.mp limit) i).mul_const _
  have dates:∀ᶠz:ℕ×ℕ in f.fuse,K<z.1:=by
    rw [Order.fused];exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop K
  apply le_of_tendsto ((physical.sub expansion).norm)
  filter_upwards [paid.filter_mono order,dates.filter_mono order] with z fare top
  obtain ⟨cofunded,continued⟩:=fare top
  have bill:=WilsonMovingForkDatedExterior.original file uv vc ck jK actual offered z top
    (fun i=>(arms i).source z) (column z) w phase cofunded (placed z.1 z.2 top)
  simp only [dif_pos (jK.trans top.le)]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (column z) _).trans (add_le_add bill continued)

end YM.Integration.WilsonMovingForkDatedProfile
end
