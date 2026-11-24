import YM.Integration.WilsonMatrixTicketLanesTerminalQWords
import YM.Integration.ActualOriginalFeeGrowth
import YM.Integration.WilsonReportingMeasuredWardFunding

/-! An authentic numerical Taylor estimate for a finite original Q roster
on its bare terminal scale, before the torus size or its source positions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQReturn
open Function Filter Finset Lattice RG Wilson Source Labels Tree FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open Precision RG17 RG12 Extraction Spec PertExtension.Series.Tested Pert.Asymptotics
open MS MS.Menus MS.Rake MS.Local.Physical
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReportedWords
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){B:Deck G}(Q:MS.Land.Prescription B){n:ℕ}(l:Fin n→Label B)

def stack {b per:ℕ}(q:ℕ)(μ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ)
    (large:Bid.Larger (G:=G) (R.family.path.levels.clock.op b per))
    (T:Forest (R.family.path.levels.clock.op b per).ratio)(u:Pins G (R.family.side b per))
    (o:Fin n→Site (R.family.side (b+1) per))(tag:(R.family.path.levels.clock.op b per).Choices)
    (v:(Descent.nil (top:=R.family.side (b+1) per)).Tags):ℂ:=
  let g:=regulatorRun R.family (b+1) per (b+1)
  ∑t:∀i,Piece R (l i),coefficient R Q l μ k reader t*(g:ℂ)^(power (word R l t))*
    peval (WilsonCoherentJointReturn.series (word R l t) (R.family.path.levels.clock.op b per)
      T R.metals.O u o large tag v) q g

def charge {b per:ℕ}(μ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ):ℝ:=
  let g:=regulatorRun R.family (b+1) per (b+1)
  ∑t:∀i,Piece R (l i),‖coefficient R Q l μ k reader t*(g:ℂ)^power (word R l t)‖

def measured {b per:ℕ}(μ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ)(u:Pins G (R.family.side b per))
    (o:Fin n→Site (R.family.side (b+1) per)):ℂ:=
  let D:=R.family.path.levels.clock.op b per
  let g:=regulatorRun R.family (b+1) per (b+1)
  (spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun U=>bare (g⁻¹^2) U • marked R Q l μ k reader o U) (Parcel.Oven.slice u g)

theorem terminal (simple:G.Simple)(paid:Paid G R.kit)(q cap:ℕ):
    ∀ᶠ b:ℕ in atTop,∀(per:ℕ)(μ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ),
      let D:=R.family.path.levels.clock.op b per
      let g:=regulatorRun R.family (b+1) per (b+1)
      ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(u:Pins G (R.family.side b per))
        (o:Fin n→Site (R.family.side (b+1) per))(tag:D.Choices)(v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
        (∀i,‖u i‖≤(cap:ℝ)+1)→
        ‖measured R Q l μ k reader u o-stack R Q l q μ k reader large T u o tag v‖≤
          charge (b:=b) (per:=per) R Q l μ k reader*(g^(q+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))):=by
  have rows (t:∀i,Piece R (l i)):=WilsonCoherentInheritedPermit.purchased R (word R l t) ((cap:ℝ)+1) q start simple paid.1
    (paid.2 (code (fun i=>(t i).1.size) (fun i=>(t i).2) q cap))
  filter_upwards [eventually_all.mpr rows] with b receipts
  intro per μ k reader D g large T u o tag v inside
  have positive:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson le_rfl))
  let c₀ (t:∀i,Piece R (l i)):=coefficient R Q l μ k reader t*(g:ℂ)^power (word R l t)
  let rate:=g^(q+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))
  have physical:=pinned R Q l μ k reader D u o g positive (R.family.path.levels.transition_mass b per (g⁻¹^2))
  have dec:(fun a b:Fin n=>Classical.propDecidable (a=b))=(inferInstance:DecidableEq (Fin n)):=Subsingleton.elim _ _
  rw [dec] at physical
  unfold measured
  rw [physical]
  dsimp only [stack,charge]
  let X (t:∀i,Piece R (l i)):=c₀ t*reads (word R l t) D u o g
  let Y (t:∀i,Piece R (l i)):=c₀ t*peval (WilsonCoherentJointReturn.series (word R l t)
    D T R.metals.O u o large tag v) q g
  change ‖(∑t,X t)-(∑t,Y t)‖≤(∑t,‖c₀ t‖)*rate
  calc
    _=‖∑t,(X t-Y t)‖:=by rw [Finset.sum_sub_distrib]
    _≤∑t:∀i,Piece R (l i),‖c₀ t‖*rate:=(norm_sum_le _ _).trans (sum_le_sum fun t _=>by
      dsimp only [X,Y]
      rw [←mul_sub,norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [rate,mul_comm] using (receipts t (b+1) per le_rfl T u o tag v inside))
    _=_:=(sum_mul ..).symm

end YM.Integration.WilsonMatrixTicketLanesTerminalQReturn
