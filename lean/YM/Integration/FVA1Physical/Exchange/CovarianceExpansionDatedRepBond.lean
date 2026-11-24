import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionOriginalRepBond
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionGradedAperture

/-! All source fees and construction data on one genuinely selected finite
history, including the first nonbare reset and later dates. All three
physical sites and all three complex calibrated coefficients are independent. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Lattice RG Wilson Precision WilsonStartup RoseCut Source Multi.Maquette Labels
open OriginalMixedWilson
open scoped Classical BigOperators
variable {G:Gauge}

theorem dated_three_source_bond (A:Family G)(selected:A.path.Selected){N n j:ℕ}(live:j<N)
    (licensed:Decent (A.path.levels.params (j+1)).clip (A.path.levels.budget (j+1)))
    (width:1≤(A.path.levels.budget (j+1)).supportExponent)
    (held:Config G (A.side j n))(e:Edge (Site (A.side (j+1) n)))(D r:ℕ)(outside:Config G (A.side (j+1) n))
    (d:Fin 3→ℕ)(w:(i:Fin 3)→(A.labels.level (d i)).Coeff)(o:Fin 3→Site (A.side (j+1) n)):
    let H:=A.path;let P:=H.rep N n (j+1);let g:=measuredCoupling P.beta;let op:=H.levels.clock.op j n
    let J:=fun z:G.El=>update outside e z
    let k:=fun z=>op.density P.beta (J z) held
    let a:=fun z=>P.eval (J z)
    let b:=fun z=>Real.exp (-(P.beta*mainTerm P.clip P.path (J z)+Precision.loop P.path (J z)))
    let pars:=H.levels.params (j+1);let cal:=H.levels.clock
    let t:=filedTolerance P.p e r (pathCash pars.width pars.paths (cal.loopCap (j+1)) P.beta D)
      (cal.forcedAllowance (j+1)) (cal.allowance (j+1))
    let E:=pairExcess (fun z=>Real.log (a z)-Real.log (b z)) t
    let fields:=fun i z=>gradedPhysicalField A (d i) (w i) g (o i) (J z)
    let L:=fun i=>gradedPhysicalCost A (d i) (w i) g
    MeasurableSet E ∧ (∀s∈E,bondObstruction P.p P.activities e D r (J s.1) (J s.2)) ∧
      sevenFare G.probHaar (fun z=>k z*a z) (fun z=>k z*b z) fields L E t:=by
  intro H P g op J k a b pars cal t E fields L
  have conv:=selected.represents N n (j+1) live
  have dec:Decent P.clip P.p:=by rw [show P.clip=pars.clip from conv.clip,show P.p=H.levels.budget (j+1) from conv.vac];exact licensed
  have support:1≤P.p.supportExponent:=by rw [show P.p=H.levels.budget (j+1) from conv.vac];exact width
  have small:cal.forcedAllowance (j+1)≤1:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  have sj:Measurable J:=by
    apply measurable_pi_lambda;intro i
    by_cases hi:i=e
    · subst i;simp only [J,update_self];intro s hs;exact hs
    simpa only [J,update_of_ne hi] using (measurable_const (a:=outside i):Measurable (fun _:G.El=>outside i))
  have price i:=graded_field_funded A (d i) (w i) g (o i)
  have env(i):Envelope (fields i):=⟨(price i).2.1.measurable.comp sj,L i,fun z=>(price i).2.2 (J z)⟩
  exact original_rep_bond op (H.levels.blocks j n).branches held P conv.good small
    (SectorNext.Vacuum.strictly H selected N n (j+1) live) dec support e D r outside fields env L
    (fun i=>(price i).1) (fun i z=>(price i).2.2 (J z))

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
