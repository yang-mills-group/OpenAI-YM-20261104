import YM.Integration.WilsonMarkedIndependentMixedIntake
import YM.Integration.WilsonMarkedIndependentEnrolledPeriod

/-! The full independently normalized source, filed at m on the compact
submitted positions, continues to the exact grouped output at any fixed
later capture j. The period threshold is independent of the top. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedCapture
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMarkedIndependentPhysicalIntake (PositiveAt PairedAt)
open WilsonMarkedIndependentMixedIntake (full)
open WilsonMarkedIndependentMixedHistory (Filed)
open WilsonMarkedIndependentOnePeriod (Course)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

def Returned (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ):Prop:=
  let L:=R.family.path.levels
  let F:=deck (G:=G) l d h
  ∀ᶠj:ℕ in atTop,∀m:ℕ,j ≤ m → ∀X:Herit F,∃ρ₀:ℝ,∀ρ:ℝ,ρ₀≤ρ →
    ∃s A:ℝ,0<s ∧ 1≤A ∧ ∀M:ℕ,∀ᶠp:ℕ in atTop,∀N,m≤N →
      PairedAt e (Gears L R.metals.O l l N m j (full R l d h X m N M ρ)) (R.family.side j p) s A

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(filed:Filed R l d h e)
    (vac:∀ᶠm:ℕ in atTop,∃s V:ℝ,0<s ∧ 1≤V ∧ ∀N p:ℕ,m≤N →
      PositiveAt R.family.path.levels R.metals.O e N m (R.family.side m p) s V):
    Returned R l d h e:=by
  let L:=R.family.path.levels
  unfold Returned
  obtain ⟨b₀,inside⟩:=eventually_atTop.mp (WilsonMarkedIndependentMixedIntake.original R simple v funded l d h e filed)
  obtain ⟨b₁,smooth⟩:=eventually_atTop.mp vac
  filter_upwards [eventually_ge_atTop b₀,eventually_ge_atTop b₁,
    FundedMarkedCoverRows.realm R simple v funded (a+1) l d h e 0 0] with j hj h₁ realm
  obtain ⟨Q,level,ratio,clock,anchor,_,_,_,_⟩:=realm
  intro m interval X
  obtain ⟨ρ₀,marked⟩:=inside m (hj.trans interval) X
  obtain ⟨t,V,positive,one,quiet⟩:=smooth m (h₁.trans interval)
  refine ⟨ρ₀,?_⟩
  intro ρ gate
  obtain ⟨w,B,hot,loaded,words⟩:=marked ρ gate
  let u:=min t w
  have uh:0<u:=lt_min positive hot
  obtain ⟨D,C,s,cp,sp,use⟩:=WilsonMarkedIndependentOnePeriod.original (D:=d) (k:=l) Q l j m anchor.le interval uh
  let A:=C*V^D*B
  have a1:1≤A:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le cp (one_le_pow₀ one)) loaded
  refine ⟨s,A,sp,a1,?_⟩
  intro M
  filter_upwards [(words M).2] with p prior
  intro N top
  let P:Course Q.draws:={side i:=R.family.side i p,next i:=by rw [level];exact Subtype.ext (L.clock.op i p).sizes}
  let Y:=full R l d h X m N M ρ
  have v₀:PositiveAt Q.draws Q.paid e N m (P.side m) u V:=by
    change PositiveAt Q.draws Q.paid e N m (R.family.side m p) u V
    rw [level,ratio]
    exact WilsonMarkedIndependentPhysicalIntake.quiet_narrow (quiet N p top) (min_le_left ..) le_rfl
  have w₀:=WilsonMarkedIndependentPhysicalIntake.narrow (prior N top) (min_le_right t w) (zero_le_one.trans loaded) le_rfl
  have reached:PairedAt e (Gears Q.draws Q.paid l l N m j Y) (R.family.side j p) s A:=
    (use N top P Y ((words M).1 N top) V B one loaded v₀ w₀).2
  rw [level,ratio] at reached
  exact reached

/-- One original lifetime, all finite orders, and a freely co-enrolled
forecast for the physical field and detector program. -/
theorem funded.{v} (simple:G.Simple){ε:ℝ}(positive:0<ε)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)
    (E:FundedCompanySelection.Prediction G)(hE:FundedPredictionSupply.AllPrices (@E)):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T),E R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{v} simple ε W ∧ ∀e:ℕ,Returned R l d h e:=by
  obtain ⟨v,quiet⟩:=WilsonVacuumPreResetFiniteHeatHierarchy.original G
  let both:=@FundedPredictionSupply.Both G (@FundedMarkedCoverRows.prices G v) (@E)
  have offer:FundedPredictionSupply.AllPrices (@both):=fun s q=>
    FundedPredictionSupply.both (FundedMarkedCoverRows.purchase v s q) (hE s q)
  obtain ⟨R,T,W,income,plateau,physical,issued⟩:=WilsonMarkedIndependentMixedHistory.funded.{v} simple positive l d h (@both) offer
  refine ⟨R,T,W,income.2,plateau,physical,?_⟩
  intro e
  apply original R simple v income.1 l d h e (issued e)
  filter_upwards [quiet R simple physical.2.2.2.2.2.2.1 income.1 e] with m data
  obtain ⟨s,V,hs,hV,row⟩:=data
  exact ⟨s,V,hs,hV,fun N p top=>(row N p top).2⟩

end YM.Integration.WilsonMarkedIndependentMixedCapture
end
