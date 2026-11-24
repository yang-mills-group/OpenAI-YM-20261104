import YM.Integration.WilsonMatrixTicketLanesTerminalQReturn

/-! An authentic numerical Taylor estimate for a finite original Q roster
at absolute grade q on the actual last bare block. The signed terms carry
different engineering degrees before the same final coupling is applied. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQGrades
open Function Filter Finset Lattice RG Wilson Source Labels Tree FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open Precision RG17 RG12 Extraction Spec PertExtension.Series.Tested Pert.Asymptotics
open MS MS.Menus MS.Rake MS.Local.Physical
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReportedWords
open WilsonMatrixTicketLanesTerminalQReturn (measured)
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
      T R.metals.O u o large tag v) (q-power (word R l t)) g

def fee (μ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ):ℝ:=
  ∑t:∀i,Piece R (l i),‖coefficient R Q l μ k reader t‖

theorem terminal (simple:G.Simple)(paid:Paid G R.kit)(q cap:ℕ)(degree:∀t:∀i,Piece R (l i),power (word R l t)≤q):
    ∀ᶠ b:ℕ in atTop,∀(per:ℕ)(μ:ℝ)(k:Fin n→ℕ)(reader:Fin n→ℂ),
      let D:=R.family.path.levels.clock.op b per
      let g:=regulatorRun R.family (b+1) per (b+1)
      ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(u:Pins G (R.family.side b per))
        (o:Fin n→Site (R.family.side (b+1) per))(tag:D.Choices)(v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
        (∀i,‖u i‖≤(cap:ℝ)+1)→
        ‖WilsonMatrixTicketLanesTerminalQReturn.measured R Q l μ k reader u o-stack R Q l q μ k reader large T u o tag v‖≤
          fee R Q l μ k reader*(g^(q+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))):=by
  have rows (t:∀i,Piece R (l i)):=WilsonCoherentInheritedPermit.purchased R (word R l t) ((cap:ℝ)+1) (q-power (word R l t)) start simple paid.1
    (paid.2 (code (fun i=>(t i).1.size) (fun i=>(t i).2) (q-power (word R l t)) cap))
  filter_upwards [eventually_all.mpr rows] with b receipts
  intro per μ k reader D g large T u o tag v inside
  have positive:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson le_rfl))
  let c₀ (t:∀i,Piece R (l i)):=coefficient R Q l μ k reader t*(g:ℂ)^power (word R l t)
  let rate:=g^(q+1)*(2+Real.log (R.family.path.levels.clock.hatBeta b))
  have physical:=pinned R Q l μ k reader D u o g positive (R.family.path.levels.transition_mass b per (g⁻¹^2))
  have dec:(fun a b:Fin n=>Classical.propDecidable (a=b))=(inferInstance:DecidableEq (Fin n)):=Subsingleton.elim _ _
  rw [dec] at physical
  unfold WilsonMatrixTicketLanesTerminalQReturn.measured
  rw [physical]
  dsimp only [stack,fee]
  let X (t:∀i,Piece R (l i)):=c₀ t*reads (word R l t) D u o g
  let Y (t:∀i,Piece R (l i)):=c₀ t*peval (WilsonCoherentJointReturn.series (word R l t)
    D T R.metals.O u o large tag v) (q-power (word R l t)) g
  change ‖(∑t,X t)-(∑t,Y t)‖≤(∑t,‖coefficient R Q l μ k reader t‖)*rate
  calc
    _=‖∑t,(X t-Y t)‖:=by rw [Finset.sum_sub_distrib]
    _≤∑t:∀i,Piece R (l i),‖coefficient R Q l μ k reader t‖*rate:=(norm_sum_le _ _).trans (sum_le_sum fun t _=>by
      dsimp only [X,Y]
      rw [←mul_sub,norm_mul]
      let w:=power (word R l t)
      let clock:=2+Real.log (R.family.path.levels.clock.hatBeta b)
      have expr:=receipts t (b+1) per le_rfl T u o tag v inside
      have bound:‖reads (word R l t) D u o g-peval (WilsonCoherentJointReturn.series (word R l t) D T
        R.metals.O u o large tag v) (q-w) g‖≤clock*g^(q-w+1):=by simpa only [clock,w,mul_comm] using expr
      apply (mul_le_mul_of_nonneg_left bound (norm_nonneg (c₀ t))).trans_eq
      have wt:=degree t
      have added:w+(q-w+1)=q+1:=by dsimp [w];omega
      dsimp only [c₀,rate]
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
      change (‖_‖*g^w)*(clock*g^(q-w+1))=‖_‖*(g^(q+1)*clock)
      rw [←added,pow_add]
      ring)
    _=_:=(sum_mul ..).symm

end YM.Integration.WilsonMatrixTicketLanesTerminalQGrades
