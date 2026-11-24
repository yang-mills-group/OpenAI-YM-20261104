import YM.Integration.WilsonMovingForkSharedResidual
import YM.Integration.WilsonMovingForkHeterogeneousCut

/-! Recenter the unrestricted aligned Wilson measurement, and hear
each compensated dated source on its actual translated prior. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.WilsonMovingForkShiftedSite
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
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {l:Ultrafilter (ℕ×ℕ)}{j n u v c K:ℕ}{d:Fin n→ℕ}{x:∀i,S.Field (d i)}
  (file:Filed R d K)(arms:∀i,Arm R.family S (l:Filter _) (d i) (x i))
  (jK:j≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K)
local notation "C" => R.family

def Reached (o shifted:Fin n → Cover)(phase:ℝ):Prop:=
  ∀N per,∀top:K<N,
    let cols:=fun i=>(arms i).source (N,per)
    let Y:=fun os:Fin n → Cover=>word R d j N per (jK.trans top.le) os cols
    ‖(C).omega N per (Y o)-reading R (N:=N) (credit (C) N per 0 (Y shifted) u
      (uv.trans (vc.trans (ck.trans top.le)))) u le_rfl‖≤phase

include F in
theorem original (order:(l:Filter _) ≤ f.fuse)(o shifted:Fin n → Cover)
    (generic:tag ((C).S.a j) o∈generic n)(I:ℂ)(phase:ℝ)(w:Invoice)
    (home:Reached arms jK uv vc ck o shifted phase)
    (filed:Heard (f:=f) file uv vc ck jK arms shifted (fun _=>I) w):
    ‖S.classMoment S d (tag ((C).S.a j) o) x-I‖≤phase+w.total v c K:=by
  have approach:=WilsonReflectedPublicAlignedPoints.aligned F order j o generic (generic_conf n generic) arms
  have late:∀ᶠ t:ℕ×ℕ in f.fuse,K<t.1:=by
    rw [Order.fused]
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop K
  apply le_of_forall_pos_le_add
  intro ε ep
  obtain ⟨t,near,paid,live⟩:=(((Metric.tendsto_nhds.mp approach) ε ep).and
      ((filed.filter_mono order).and (late.filter_mono order))).exists
  let col:=fun i=>(arms i).source t
  let Y:=fun os:Fin n → Cover=>word R d j t.1 t.2 (jK.trans live.le) os col
  have trueField:‖S.classMoment S d (tag ((C).S.a j) o) x-(C).omega t.1 t.2 (Y o)‖≤ε:=by
    simp only [dif_pos (jK.trans live.le)] at near
    change dist ((C).omega t.1 t.2 (Y o)) _<ε at near
    simpa [dist_eq_norm,norm_sub_rev] using near.le
  obtain ⟨ok,upper,fine,across,coarse,bottom⟩:=paid live
  let q:=doses R d file.station (N:=t.1) (per:=t.2) (file.A t.1 t.2) col
  let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jK t.2 shifted
  let bank:=file.row t.1 t.2 q ξ
  have cont:Continuous (Y shifted):=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  have measure:=fixed R uv vc ck live.le (Y shifted) cont bank ok I
  dsimp only at measure
  have entry:entrance R (Y shifted) (uv.trans (vc.trans ck)) live.le bank≤w.upper:=by
    unfold entrance
    change ‖_-reading R (N:=t.1) (numerator R t.1 t.2 K (file.row t.1 t.2 q ξ K)) u _‖≤w.upper
    rw [file.seed t.1 t.2 live]
    exact upper
  have cost:=measure.trans (add_le_add (add_le_add (add_le_add (add_le_add entry
    (sum_le_sum fine)) across) (sum_le_sum coarse)) bottom)
  have moved:=home t.1 t.2 live
  have bound:‖S.classMoment S d (tag ((C).S.a j) o) x-I‖≤ε+(phase+w.total v c K):=by
    exact (norm_sub_le_norm_sub_add_norm_sub _ ((C).omega t.1 t.2 (Y o)) _).trans
      ((add_le_add trueField ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add moved cost))).trans_eq
        (by unfold Invoice.total;ring))
  linarith only [bound]

end YM.Integration.WilsonMovingForkShiftedSite
