import YM.Integration.WilsonMatrixTicketLanesTerminalQAmplitude

/-! Coefficients of the same finite-temperature first-block readings, before the period or pin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQCoefficients
open Function Filter Finset Lattice RG Wilson Source Labels Tree FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open Precision RG17 RG12 Extraction Spec PertExtension.Series.Tested Pert.Asymptotics
open MS MS.Menus MS.Rake MS.Local.Physical
open WilsonMatrixTicketLanesTerminalQWords WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReportedWords
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){B:Deck G}{n:ℕ}(l:Fin n→Label B)

private theorem adjacent (a:ℕ→ℂ)(z:ℂ)(k:ℕ){g L:ℝ}(gp:0<g)
    (prev:‖z-peval a k g‖≤g^(k+1)*L)
    (next:‖z-peval a (k+1) g‖≤g^(k+1+1)*L):
    ‖a (k+1)‖≤(1+g)*L:=by
  have series:peval a (k+1) g=peval a k g+g^(k+1) • a (k+1):=sum_range_succ ..
  have term:g^(k+1) • a (k+1)=(z-peval a k g)-(z-peval a (k+1) g):=by rw [series];abel
  apply (le_of_mul_le_mul_left ?_ (pow_pos gp (k+1)))
  calc
    _=‖g^(k+1) • a (k+1)‖:=by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos gp _)]
    _≤g^(k+1)*L+g^(k+1+1)*L:=by rw [term];exact (norm_sub_le ..).trans (add_le_add prev next)
    _=g^(k+1)*((1+g)*L):=by rw [pow_succ g (k+1)];ring

theorem purchased (simple:G.Simple)(paid:Paid G R.kit)(q cap:ℕ):
    ∃C:ℝ,0≤C ∧ ∀ᶠ b:ℕ in atTop,∀per:ℕ,
      let D:=R.family.path.levels.clock.op b per
      let g:=regulatorRun R.family (b+1) per (b+1)
      let clock:=2+Real.log (R.family.path.levels.clock.hatBeta b)
      ∀(large:Bid.Larger (G:=G) D)(T:Forest D.ratio)(u:Pins G (R.family.side b per))
        (o:Fin n→Site (R.family.side (b+1) per))(tag:D.Choices)(v:(Descent.nil (top:=R.family.side (b+1) per)).Tags),
        (∀i,‖u i‖≤(cap:ℝ)+1)→∀t:∀i,Piece R (l i),
        let J:=word R l t
        let a:=WilsonCoherentJointReturn.series J D T R.metals.O u o large tag v
        ‖a 0‖≤g⁻¹^(power J)*C+g*clock ∧ ∀k:ℕ,k+1≤q→‖a (k+1)‖≤(1+g)*clock:=by
  choose A pos bound using fun t:∀i,Piece R (l i)=>WilsonMatrixTicketLanesTerminalQAmplitude.compact (word R l t)
  let C:=∑t,A t
  have cp:0≤C:=sum_nonneg fun t _=>pos t
  have each (t:∀i,Piece R (l i)) (k:Fin (q+1)):=WilsonCoherentInheritedPermit.purchased R (word R l t)
    ((cap:ℝ)+1) k.val start simple paid.1 (paid.2 (code (fun i=>(t i).1.size) (fun i=>(t i).2) k.val cap))
  refine ⟨C,cp,?_⟩
  filter_upwards [eventually_all.2 fun t=>eventually_all.2 (each t)] with b receipts
  intro per D g clock large T u o tag v inside t J a
  have gp:0<g:=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have price (j:ℕ)(jh:j≤q):‖reads J D u o g-peval a j g‖≤g^(j+1)*clock:=
    receipts t ⟨j,by omega⟩ (b+1) per le_rfl T u o tag v inside
  constructor
  · have gross:=WilsonMatrixTicketLanesTerminalQAmplitude.normalized J (pos t) (bound t) D u o gp
      (R.family.path.levels.transition_mass b per (g⁻¹^2))
    have zero:‖reads J D u o g-a 0‖≤g*clock:=by simpa [peval,PertExtension.Series.Zone.eval] using price 0 (Nat.zero_le q)
    have size:A t≤C:=single_le_sum (fun i _=>pos i) (mem_univ t)
    calc
      _≤‖reads J D u o g‖+‖a 0-reads J D u o g‖:=by
        simpa only [add_sub_cancel] using norm_add_le (reads J D u o g) (a 0-reads J D u o g)
      _≤_:=by rw [norm_sub_rev];exact add_le_add (gross.trans (mul_le_mul_of_nonneg_left size
        (pow_nonneg (inv_pos.mpr gp).le _))) zero
  · intro k hk
    exact adjacent a _ k gp (price k (by omega)) (price _ hk)

end YM.Integration.WilsonMatrixTicketLanesTerminalQCoefficients
