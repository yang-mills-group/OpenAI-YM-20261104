import YM.Integration.WilsonMarkedIndependentMixedEnrollment
import YM.Integration.WilsonMarkedIndependentMixedStep
import YM.Integration.WilsonMarkedIndependentNormalizedHistory

/-! Finite-period winding for inverse-normalized marked sources whose genuine
microscopic birth is at the moving UV cutoff. The report admits each separated
external roster with all its proper subsets, angular scalars and subcell lifts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedHistory
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentNormalizedHistory (planted)
open WilsonMarkedIndependentMixedStep (Entries)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

def Filed (R:Run G)(l d:Fin (a+1)→ℕ)(eligible:∀i,l i<d i)(e:ℕ):Prop:=
  let L:=R.family.path.levels
  let F:=deck (G:=G) l d eligible
  ∃C W:Credit,∀ᶠm:ℕ in atTop,∀X:Herit F,
    let z:=zz L m+∑i,C.buy (zz L m)*fee (F i) (X i) e
    let B:=W.buy z
    1≤B ∧ ∀ρ:ℝ,galeGate G d l l e W Credit.leanC Credit.leanC z≤ρ →
      ∀N p j:ℕ,m≤j → j≤N →
        Entries (Gears L R.metals.O l l N N j (planted R l d eligible X m N))
          L.S m j p e ρ B (rate L j p)

/-- One reporting wallet prices the entire signed history on each original
period, uniformly in the cutoff and all later dates. -/
theorem original (l d:Fin (a+1)→ℕ)(eligible:∀i,l i<d i):
    ∃(v₀ v:ℕ→Gear G→ℝ),∀(R:Run G),G.Simple →
    RG05Preconstruction.ReadoutPurchase R.b → FundedMarkedCoverRows.prices v₀ R.kit →
    FundedMarkedCoverRows.prices v R.kit → ∀e:ℕ,Filed R l d eligible e:=by
  obtain ⟨v₀,quiet⟩:=WilsonVacuumPreResetFiniteHeatHierarchy.original G
  choose w stage using fun e=>WilsonMarkedIndependentMixedStep.original (G:=G) d l l e
  let v(J:ℕ)(I:Gear G):=∑e∈range (J+1),|w e I|
  have dominates(J e:ℕ)(he:e≤J)(I:Gear G):w e I≤v J I:=
    (le_abs_self _).trans (Finset.single_le_sum (f:=fun e=>|w e I|) (fun _ _=>abs_nonneg _)
      (mem_range.mpr (by omega)))
  refine ⟨v₀,v,?_⟩
  intro R simple readout fundQuiet funded e
  let L:=R.family.path.levels
  let F:=deck (G:=G) l d eligible
  obtain ⟨C,W,roster⟩:=WilsonMarkedIndependentMixedEnrollment.original R simple v funded l d eligible e
  obtain ⟨q₀,hq⟩:=eventually_atTop.mp (quiet R simple readout fundQuiet e)
  obtain ⟨w₀,ready⟩:=eventually_atTop.mp (stage e R simple W)
  have grows:Tendsto (fun j:ℕ=>L.clock.J (j+1)) atTop atTop:=L.fits.deep.comp (tendsto_add_atTop_nat 1)
  obtain ⟨g₀,active⟩:=eventually_atTop.mp (grows.eventually_ge_atTop e)
  refine ⟨C,W,?_⟩
  filter_upwards [roster,eventually_ge_atTop q₀,eventually_ge_atTop w₀,eventually_ge_atTop g₀] with m raw hqm hwm hgm
  obtain ⟨Q,level,scheme,clock,anchor,cloze,stored,teacher⟩:=raw
  intro X z B
  let U(N:ℕ):=normalized Q.draws Q.paid F X m N
  let P(N:ℕ):=coatA Q.draws Q.paid N m F (U N)
  have source(N:ℕ)(live:m≤N):Borealis Q d l l (P N) m N W z:=teacher X N live
  have bpos:1≤B:=W.purchase ((Q.depth m anchor.le).trans (source m le_rfl).yell)
  refine ⟨bpos,?_⟩
  intro ρ clear N p j mj upto
  have atN:=mj.trans upto
  have chosen:P N=planted R l d eligible X m N:=by dsimp only [P,U,planted];rw [level,scheme]
  let K(i:ℕ):=Gears Q.draws Q.paid l l N N i (P N)
  have march (t:ℕ):∀j:ℕ,m≤j → j+t=N →
      Entries (K j) L.S m j p e ρ B (rate L j p):=by
    induction t with
    | zero=>
      intro j _ stop
      have jN:j=N:=by omega
      subst j
      intro I y _ _ _ i _ r x
      dsimp only [K]
      rw [gearTop]
      have top:=WilsonMarkedIndependentNormalizedTop.original F Q.draws Q.paid N m (U N) y I (R.family.side N p) i r
      change WilsonCoeffUV.Bank.Carp.plume ((P N y I).2 i r) _=(P N y I).1 _ i r at top
      rw [top,sub_self,norm_zero];exact mul_nonneg (pow_nonneg (zero_le_one.trans bpos) _) (Real.exp_pos _).le
    | succ t ih=>
      intro j above stop
      have ca:Q.anchor≤j:=anchor.le.trans above
      have J:=active j (hgm.trans above)
      have receipt:=(stored j above ca).choose_spec.2
      have price:w e (Q.mint j ca).gear≤Q.cash Credit.leanC j:=(dominates _ e J _).trans receipt
      obtain ⟨_,_,_,_,vac⟩:=hq (j+1) (by omega)
      exact ready j (hwm.trans above) Q ca level scheme clock price m N p above (by omega)
        (P N) z ρ (source N atN) cloze clear (vac N p (by omega)).1 (ih (j+1) (by omega) (by omega))
  have checked:=march (N-j) j mj (by omega)
  dsimp only [K] at checked
  rw [chosen,level,scheme] at checked
  exact checked

/-- The original selected R/T/W carry all finite accuracies and any other
enrolled forecast on the same lifetime, before either regulator is selected. -/
theorem funded.{v} (simple:G.Simple){ε:ℝ}(hε:0<ε)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)
    (E:FundedCompanySelection.Prediction G)(hE:FundedPredictionSupply.AllPrices (@E)):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),E R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{v} simple ε W ∧ ∀e:ℕ,Filed R l d h e:=by
  obtain ⟨v₀,v,grant⟩:=original (G:=G) l d h
  let both:=@FundedPredictionSupply.Both G (@FundedMarkedCoverRows.prices G v₀) (@E)
  have combined:FundedPredictionSupply.AllPrices (@both):=
    fun S q=>FundedPredictionSupply.both (FundedMarkedCoverRows.purchase v₀ S q) (hE S q)
  obtain ⟨R,T,W,paid,extra,plateau,originalRun⟩:=FundedMarkedCoverRows.original.{v} simple hε v (@both) combined
  exact ⟨R,T,W,extra.2,plateau,originalRun,grant R simple originalRun.2.2.2.2.2.2.1 extra.1 paid⟩


end YM.Integration.WilsonMarkedIndependentMixedHistory
end
