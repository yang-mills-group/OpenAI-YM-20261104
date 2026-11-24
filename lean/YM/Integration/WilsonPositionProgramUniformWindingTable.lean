import YM.Integration.WilsonPositionProgramUniformWindingCapture
import YM.Integration.WilsonMarkedIndependentMixedIntegratedHistory
/-! Finite winding on the complete ordinary center-integrated program for
any sequence of admitted numerical coordinates and internal cutoffs. -/
set_option warningAsError true
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramUniformWindingTable
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Layout
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Winding WilsonCoeffUV.Blue Source Source.Drops Labels MeasureTheory
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentMixedIntake (full)
open WilsonMarkedIndependentMixedMomentTensor (Tensor)
open WilsonPositionProgramUniformWindingCapture (Returned)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

def Complete (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(T:Credit)(δ:ℝ):Prop:=
  let F:=deck (G:=G) l d h
  let L:=R.family.path.levels
  let O:=R.metals.O
  ∀ᶠb:ℕ in atTop,∀m:ℕ,b ≤ m → ∃s:ℝ,0<s ∧
    ∀(fields:ℕ→Herit F)(tops:ℕ→ℕ), (∀q, m≤q → m≤tops q) →
      (∀q,m≤q → ∀i,fee (F i) (fields q i) e≤T.buy (zz L m)) → ∀φ:Wilt F,(∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
      (∀y:ℝ,Tensor G Lounge m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
        (fun q=>LodeStar L O φ (normalized L O F (fields q) m (tops q)) m b (tops q) y)) ∧
      ∀D:ℕ,Tensor G (Vote D) m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
        (fun q=>AutumnDay L O φ (normalized L O F (fields q) m (tops q)) m b (tops q) D)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(T:Credit){δ:ℝ}(captured:Returned R l d h e T δ):
    Complete R l d h e T δ:=by
  let L:=R.family.path.levels
  let O:=R.metals.O
  let F:=deck (G:=G) l d h
  obtain ⟨f,hire⟩:=eventually_atTop.mp (FundedMarkedCoverRows.realm R simple v funded (a+1) l d h e 0 0)
  unfold Complete
  filter_upwards [captured,eventually_ge_atTop f] with b event fb
  intro m bm
  let ρ:=δ*longLog L m
  obtain ⟨Q,level,scheme,_,anchor,_,_,⟨tribe⟩,_⟩:=hire m (fb.trans bm)
  obtain ⟨s,A,hs,hA,posted⟩:=event m bm
  refine ⟨s,hs,?_⟩
  intro fields tops mature budget φ clear
  have measured(y:ℝ):Tensor G Lounge m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
      (fun q=>LodeStar L O φ (normalized L O F (fields q) m (tops q)) m b (tops q) y):=by
    let M:=WilsonMarkedIndependentMixedMeasurement.span φ y 1
    let Y(q:ℕ):=Gears L O l l (tops q) m b (full R l d h (fields q) m (tops q) M ρ)
    have growing:Tendsto (fun p:ℕ=>(R.family.side b p).val) atTop atTop:=
      (show StrictMono (fun p:ℕ=>(R.family.side b p).val) from fun _ _ h=>
        Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator b).pos).tendsto_atTop
    have before:= (posted M).mono fun p shared q hq=>shared (fields q) (budget q hq) (tops q) (mature q hq)
    have rows:=WilsonMarkedIndependentMixedCenterTensor.measured (u:=paceT L.S m b) (y:=y) (k:=l) φ Y growing hs hA before
    apply WilsonMarkedIndependentMixedMomentMeasure.agree _ rows
    intro q hq
    apply WilsonMarkedIndependentMixedCenterTensor.separate
    intro z
    rw [WilsonMarkedIndependentMixedCenterTensor.center]
    have same:=WilsonMarkedIndependentMixedMeasurement.lode Q (hol G) F tribe m (tops q) b M anchor.le (mature q hq) bm
      (normalized L O F (fields q) m (tops q)) φ z y ρ le_rfl clear
    have rank:asp F=l:=rfl
    simpa only [Y,full,WilsonMarkedIndependentNormalizedHistory.planted,outset,level,scheme,rank,L,O,F,deck,Patrol.BayV] using same
  exact ⟨measured,fun D=>WilsonMarkedIndependentMixedIntegratedHistory.tensor (HourFace dayMeasure D) (measured (paceT L.S m b))⟩

theorem funded.{v} (simple:G.Simple){ε:ℝ}(positive:0<ε)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)
    (E:FundedCompanySelection.Prediction G)(hE:FundedPredictionSupply.AllPrices (@E)):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),E R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{v} simple ε W ∧ ∀e H δ,0<δ → Complete R l d h e H δ:=by
  obtain ⟨v,quiet⟩:=WilsonVacuumPreResetFiniteHeatHierarchy.original G
  let both:=@FundedPredictionSupply.Both G (@FundedMarkedCoverRows.prices G v) (@E)
  have offer:FundedPredictionSupply.AllPrices (@both):=fun s q=>FundedPredictionSupply.both (FundedMarkedCoverRows.purchase v s q) (hE s q)
  obtain ⟨R,T,W,income,plateau,truth,issued⟩:=WilsonMarkedIndependentMixedHistory.funded.{v} simple positive l d h (@both) offer
  refine ⟨R,T,W,income.2,plateau,truth,?_⟩
  intro e U δ hd
  apply original R simple v income.1 l d h e U
  apply WilsonPositionProgramUniformWindingCapture.original R simple v income.1 l d h e (issued e) U hd
  filter_upwards [quiet R simple truth.2.2.2.2.2.2.1 income.1 e] with m data
  obtain ⟨s,V,hs,hV,row⟩:=data
  exact ⟨s,V,hs,hV,fun N p low=>(row N p low).2⟩

end YM.Integration.WilsonPositionProgramUniformWindingTable
end
