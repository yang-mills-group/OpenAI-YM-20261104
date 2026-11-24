import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRestoredRegionalHearing

/-! Conditional physical hearing at the same measured coupling. This branch
uses the literal uncut kinetic, path-polynomial and loop bank of a lawful
physical RG representation. Its full regular and compulsory OLD sectors
and scalar offset are included in the original density. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Lattice RG Wilson Precision WilsonStartup RoseCut
open scoped Classical BigOperators
variable {G:Gauge}{c n:Side}
local notation "Fld" => Config G n

theorem original_rep_bond (op:StepData c n)(branch:op.patch.Branches op.kernel G)(held:Config G c)
    (R:Rep G n){σ C Λ ε w:ℝ}(law:R.Lawful σ C Λ ε w)(small:w≤1)
    (live:∀U,0<R.eval U)(licensed:Decent R.clip R.p)(width:1≤R.p.supportExponent)
    (e:Edge (Site n))(D r:ℕ)(outside:Fld)(h:Fin 3→G.El→ℂ)(eh:∀i,Envelope (h i))
    (L:Fin 3→ℝ)(ln:∀i,0≤L i)(cash:∀i x,‖h i x‖≤L i):
    let J:=fun z:G.El=>update outside e z
    let k:=fun z=>op.density R.beta (J z) held
    let a:=fun z=>R.eval (J z)
    let b:=fun z=>Real.exp (-(R.beta*mainTerm R.clip R.path (J z)+Precision.loop R.path (J z)))
    let t:=filedTolerance R.p e r (pathCash σ C Λ R.beta D) w ε
    let E:=pairExcess (fun z=>Real.log (a z)-Real.log (b z)) t
    MeasurableSet E ∧ (∀s∈E,bondObstruction R.p R.activities e D r (J s.1) (J s.2)) ∧
      sevenFare G.probHaar (fun z=>k z*a z) (fun z=>k z*b z) h L E t:=by
  intro J k a b t E
  let rank:Empty→ℕ:=fun _=>0
  let bank:(v:Empty)→ℕ→Atom G (rank v):=fun v=>nomatch v
  let coef:Empty→ℝ:=fun _=>0
  have gp(U:Fld):0<R.activities.gas R.p U:=
    (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (show 0<Real.exp (R.exponent U)*R.activities.gas R.p U from live U)
  have eq(U:Fld):Real.exp (R.v*Fintype.card (Site n)-R.activities.additive R.p U)*
      (Real.exp (-(R.path.inChannels R.clip R.p R.beta U))*R.activities.gas R.p U)=R.eval U:=by
    unfold Rep.eval Rep.exponent
    rw [←mul_assoc,←Real.exp_add];congr 2;ring
  have price:=restored_regional_hearing op branch held R.p R.clip R.path law.paths licensed R.beta rank bank coef []
    (s':=1) (B:=0) (by norm_num) (fun v=>nomatch v) (fun v=>nomatch v)
    e D r outside R.activities R.activities law.labels small gp law.labels width (R.v*Fintype.card (Site n))
    h eh L ln cash
  simpa only [fullPhysical,fullIndependent,passengerCash,List.map_nil,List.sum_nil,add_zero,eq]
    using price

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
