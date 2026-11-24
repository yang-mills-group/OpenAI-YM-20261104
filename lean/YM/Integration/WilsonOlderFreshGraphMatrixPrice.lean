import YM.Integration.WilsonOlderFreshGraphSubmit
import YM.Integration.WilsonPhysicalHistoryPriorSelection
import YM.Integration.WilsonWindowVacuumLaws

/-! The real index-specific compiler fee is fixed before the block. The
true seed is chosen below both the published radius and the reciprocal of
that fee. A jointly purchased original aperture bounds its square by the
log of the measured forecast on the same run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphMatrixPrice
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical

open WilsonOlderFreshGraphCompiler
def printer (G:Gauge) (I:Unit→Loan) (d Q:ℕ) (level:(I ()).toll=d) (K:KernelChoices)(x:ℕ):
    WilsonOlderFreshGraphCompiler.Press G I d Q (WilsonOlderFreshGraphPainter.width G K d Q x):=
  before_block G d Q (WilsonOlderFreshGraphPainter.width G K d Q x) I level
    (div_pos ((windowBasis G K).pos x) (by positivity))

def menu (G:Gauge) (I:Unit→Loan) (d Q:ℕ) (level:(I ()).toll=d):WilsonOlderFreshGraphSchool.Menu where
  width:=fun _ _ K _ x=>min (strip I Q (WilsonOlderFreshGraphPainter.width G K d Q x))
    (1+(printer G I d Q level K x).cap)⁻¹
  positive:=fun _ _ K _ x=>lt_min (Agenda.solid {()} I Q
    (div_pos ((windowBasis G K).pos x) (by positivity)) (Q+1))
    (inv_pos.mpr (by linarith [(printer G I d Q level K x).positive]))
  shell:=fun _=>1
  cost:=fun _=>zero_lt_one

def jointLaw {G:Gauge} {φ:ℕ→ℕ} (law:VowsR.LawScroll G φ):VowsR.LawScroll G φ:=
  MintClock.both G φ law (WilsonPhysicalHistoryPriorAperture.law G φ)

theorem prepared {G:Gauge} (simple:G.Simple){φ:ℕ→ℕ} (I:Unit→Loan)(d Q:ℕ)(level:(I ()).toll=d)
    (law:VowsR.LawScroll G φ) (U:ℕ→ℕ)
    (ready:∀(s:Sheet G)(q:MapPrices),WilsonWindowBookPurchase.Permitted law s (ThroughLaunch.raging s q)):
    AllPrices (Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G I d Q level) simple (jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U)):=fun s q=>
  joint (WilsonOlderFreshGraphSchool.before_period (menu G I d Q level) simple (jointLaw law)
    (fun s q=>WilsonWindowVacuumLaws.both (ready s q) (WilsonPhysicalHistoryPriorSelection.permitted φ s _)) s q)
    (WilsonWindowFormalPurchase.prepaid U s _)

theorem on_run {G:Gauge} (simple:G.Simple) (R:Run G) {φ U:ℕ→ℕ}(I:Unit→Loan)(d Q:ℕ)
    (level:(I ()).toll=d) (law:VowsR.LawScroll G φ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G I d Q level) simple (jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit):
    let M:=menu G I d Q level
    let H:=roots M simple R.metals.p R.metals.K
    (∃ B,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) B) ∧
    ∀(b k:ℕ),k ≤ R.alloy.B.a.clock.J (b+1)→1 ≤ Burn.horizon k→
      let i:=R.alloy.B.a.clock.J (b+1)
      let σ:=Agenda.seed H φ (Burn.horizon k) i
      let K:=R.metals.p.kernel
      2*σ ≤ strip I Q (WilsonOlderFreshGraphPainter.width G K d Q i) ∧
      (1+(printer G I d Q level K i).cap)^2 ≤ Real.log (R.alloy.B.a.clock.hatBeta (b+1)):=by
  intro M H
  obtain ⟨⟨books,school⟩,gated⟩:=WilsonOlderFreshGraphSchool.on_run M simple (jointLaw law) R purchase.1
  have before:WilsonPhysicalHistoryPriorAperture.Paid R.rolls H φ R.alloy.delay:=school.obligation.2
  refine ⟨⟨books,{school with obligation:=school.obligation.1}⟩,?_⟩
  intro b k fit hk i σ K
  let A:=strip I Q (WilsonOlderFreshGraphPainter.width G K d Q i)
  let g:=(printer G I d Q level K i).cap
  have σpos:0<σ:=Agenda.stem H φ (Burn.horizon k) i
  have g0:0≤g:=(printer G I d Q level K i).positive
  have hg:0<1+g:=by linarith
  have h:=gated (Burn.horizon k) i hk
  change σ ≤ min A (1+g)⁻¹/(16*1) at h
  have hA:=min_le_left A (1+g)⁻¹
  have hG:=min_le_right A (1+g)⁻¹
  refine ⟨by change 2*σ ≤ A;linarith,?_⟩
  have inv:σ ≤ (1+g)⁻¹:=by linarith
  have fees:1+g ≤ σ⁻¹:=(le_inv_comm₀ hg σpos).mpr inv
  exact (pow_le_pow_left₀ hg.le fees 2).trans
    (WilsonPhysicalHistoryPriorAperture.on_run simple R H φ before b k fit)
end YM.Integration.WilsonOlderFreshGraphMatrixPrice
end
