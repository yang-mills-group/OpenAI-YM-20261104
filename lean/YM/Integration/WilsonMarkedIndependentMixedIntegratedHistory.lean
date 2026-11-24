import YM.Integration.WilsonMarkedIndependentMixedScheduledCapture
import YM.Integration.WilsonMarkedIndependentMixedCenterTensor

/-! Complete finite/cover return on the same original center. The center
integral and the child test keep the original within-cell coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedIntegratedHistory
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
open WilsonMarkedIndependentMixedScheduledCapture (Returned)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

theorem tensor {U V:Type}[NormedAddCommGroup U][NormedSpace ℝ U][NormedAddCommGroup V][NormedSpace ℝ V]
    {m e:ℕ}{n:ℕ→Side}{t:ℕ→ℝ}{Y:ℕ→Era G U}(M:U→L[ℝ]V)(h:Tensor G U m e n t Y):
    Tensor G V m e n t (fun N=>tuftV M (Y N)):=fun i hi r x=>WilsonMarkedIndependentMixedMomentPrice.mapped M (h i hi r x)

def Complete (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(T:Credit)(δ:ℝ):Prop:=
  let F:=deck (G:=G) l d h
  let L:=R.family.path.levels
  let O:=R.metals.O
  ∀ᶠb:ℕ in atTop,∀m:ℕ,b ≤ m → ∀X:Herit F,(∀i,fee (F i) (X i) e≤T.buy (zz L m)) →
    ∃s:ℝ,0<s ∧ ∀φ:Wilt F,(∀i j,i≠j → ClearDay (φ i) (φ j) (δ*longLog L m+14)) →
      (∀y:ℝ,Tensor G Lounge m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
        (fun N=>LodeStar L O φ (normalized L O F X m N) m b N y)) ∧
      ∀D:ℕ,Tensor G (Vote D) m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
        (fun N=>AutumnDay L O φ (normalized L O F X m N) m b N D)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(T:Credit){δ:ℝ}(captured:Returned R l d h e T δ):
    Complete R l d h e T δ:=by
  let L:=R.family.path.levels
  let O:=R.metals.O
  let F:=deck (G:=G) l d h
  obtain ⟨f,hire⟩:=eventually_atTop.mp (FundedMarkedCoverRows.realm R simple v funded (a+1) l d h e 0 0)
  unfold Complete
  filter_upwards [captured,eventually_ge_atTop f] with b event fb
  intro m bm X budget
  let ρ:=δ*longLog L m
  obtain ⟨Q,level,scheme,_,anchor,_,_,⟨tribe⟩,_⟩:=hire m (fb.trans bm)
  obtain ⟨s,A,hs,hA,posted⟩:=event m bm X budget
  refine ⟨s,hs,?_⟩
  intro φ clear
  have measured(y:ℝ):Tensor G Lounge m e (R.family.side b) (fun p=>catchW s (R.family.side b p))
      (fun N=>LodeStar L O φ (normalized L O F X m N) m b N y):=by
    let M:=WilsonMarkedIndependentMixedMeasurement.span φ y 1
    let Y(N:ℕ):=Gears L O l l N m b (full R l d h X m N M ρ)
    have growing:Tendsto (fun p:ℕ=>(R.family.side b p).val) atTop atTop:=
      (show StrictMono (fun p:ℕ=>(R.family.side b p).val) from fun _ _ h=>
        Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator b).pos).tendsto_atTop
    have rows:=WilsonMarkedIndependentMixedCenterTensor.measured (u:=paceT L.S m b) (y:=y) (k:=l) φ Y growing hs hA (posted M)
    apply WilsonMarkedIndependentMixedMomentMeasure.agree _ rows
    intro N top
    apply WilsonMarkedIndependentMixedCenterTensor.separate
    intro z
    rw [WilsonMarkedIndependentMixedCenterTensor.center]
    have same:=WilsonMarkedIndependentMixedMeasurement.lode Q (hol G) F tribe m N b M anchor.le top bm
      (normalized L O F X m N) φ z y ρ le_rfl clear
    have rank:asp F=l:=rfl
    simpa only [Y,full,WilsonMarkedIndependentNormalizedHistory.planted,outset,level,scheme,rank,L,O,F,deck,Patrol.BayV] using same
  exact ⟨measured,fun D=>tensor (HourFace dayMeasure D) (measured (paceT L.S m b))⟩

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
  apply WilsonMarkedIndependentMixedScheduledCapture.original R simple v income.1 l d h e (issued e) U hd
  filter_upwards [quiet R simple truth.2.2.2.2.2.2.1 income.1 e] with m data
  obtain ⟨s,V,hs,hV,row⟩:=data
  exact ⟨s,V,hs,hV,fun N p low=>(row N p low).2⟩

end YM.Integration.WilsonMarkedIndependentMixedIntegratedHistory
end
