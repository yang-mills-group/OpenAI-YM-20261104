import YM.Integration.WilsonMovingForkDatedProfile
import YM.Integration.WilsonMovingForkPrintedFile

/-! Signed quadratures of genuinely different occupied subfaces share one
original optical inverse and a fixed pair of older receivers. The finite
independent port supplies its single scalar after the subtraction. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.WilsonMovingForkDatedContrast
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

open WilsonMovingForkPrintedFile (Program row)
variable {G:Gauge}{R:Run G}{n K:ℕ}{d:Fin n → ℕ}
local notation "C" => R.family

/-- Restrict the purchased matrices and then plant this face's full independent
programme. The matrices have no dependence on the translated ports. -/
def face (master:Filed R d K){m:ℕ}(pick:Fin m → Fin n)(prog:Program R (fun i=>d (pick i)) K):
    Filed R (fun i=>d (pick i)) K where
  station:=fun i=>master.station (pick i)
  target:=master.target
  before:=fun i=>master.before (pick i)
  A:=fun N per i=>master.A N per (pick i)
  arrived:=fun N per top i=>master.arrived N per top (pick i)
  row:=row prog
  seed:=by intro N per live w ξ;funext U;simp [row]

variable {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}
  {j u v c:ℕ}{fields:∀i,S.Field (d i)}(arms:∀i,Arm R.family S (l:Filter _) (d i) (fields i))
  (master:Filed R d K)

include F in
theorem original (order:(l:Filter _)≤f.fuse)(jK:j≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K)
    {I:Type}[Fintype I](m:I → ℕ)(pick:∀a,Fin (m a) → Fin n)
    (prog:∀a,Program R (fun i=>d (pick a i)) K)
    (actual offered:∀a,Fin (m a) → Cover)(generic:∀a,tag ((C).S.a j) (actual a)∈generic (m a))
    (μ:I → ℂ)(phase:I → ℝ)(wallet:I → Invoice)(terminal:I → (ℕ×ℕ) → ℂ)(tail:ℝ)
    (placed:∀a,Reached (R:=R) (fun i=>arms (pick a i)) jK uv vc ck (actual a) (offered a) (phase a))
    (paid:∀ᶠz:ℕ×ℕ in f.fuse,∀top:K<z.1,∀a,
      At (face master (pick a) (prog a)) uv vc ck jK (offered a) z top
        (fun i=>(arms (pick a i)).source z) (terminal a z) (wallet a))
    (combined:∀ᶠz:ℕ×ℕ in f.fuse,‖∑a,μ a*terminal a z‖≤tail):
    ‖∑a,μ a*S.classMoment S (fun i=>d (pick a i)) (tag ((C).S.a j) (actual a)) (fun i=>fields (pick a i))‖≤
      (∑a,‖μ a‖*(phase a+(wallet a).total v c K))+tail:=by
  let Y:=fun a (z:ℕ×ℕ)=>(C).ensemble (fun i=>d (pick a i))
    (fun i=>if h:j≤z.1 then ((C).S.toDepth h z.2).embed (wrap _ (actual a i)) else 0)
    (fun i=>(arms (pick a i)).source z)
  have land:=fun a=>WilsonReflectedPublicAlignedPoints.aligned F order j (actual a) (generic a)
    (generic_conf _ (generic a)) (fun i=>arms (pick a i))
  have approach:=tendsto_finsetSum Finset.univ (fun a _=>(tendsto_const_nhds (x:=μ a)).mul (land a))
  apply le_of_tendsto approach.norm
  have dates:∀ᶠz:ℕ×ℕ in f.fuse,K<z.1:=by
    rw [Order.fused];exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop K
  filter_upwards [dates.filter_mono order,paid.filter_mono order,combined.filter_mono order] with z live audited normalized
  have earned(a):‖Y a z-terminal a z‖≤phase a+(wallet a).total v c K:=by
    simp only [Y,dif_pos (jK.trans live.le)]
    exact WilsonMovingForkDatedExterior.original (face master (pick a) (prog a)) uv vc ck jK (actual a)
      (offered a) z live (fun i=>(arms (pick a i)).source z) (terminal a z) (wallet a) (phase a) (audited live a)
      (placed a z.1 z.2 live)
  have fees:‖(∑a,μ a*Y a z)-∑a,μ a*terminal a z‖≤∑a,‖μ a‖*(phase a+(wallet a).total v c K):=by
    rw [←Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _=>?_ )
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (earned i) (norm_nonneg _)
  change ‖∑a,μ a*Y a z‖≤_
  exact (show ‖∑a,μ a*Y a z‖≤‖(∑a,μ a*Y a z)-∑a,μ a*terminal a z‖+‖∑a,μ a*terminal a z‖ by
    simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (∑a,μ a*Y a z) (∑a,μ a*terminal a z) 0).trans
    (add_le_add fees normalized)

end YM.Integration.WilsonMovingForkDatedContrast
end
