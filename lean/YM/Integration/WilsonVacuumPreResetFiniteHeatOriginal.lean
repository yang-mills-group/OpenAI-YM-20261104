import YM.Integration.WilsonVacuumPreResetFiniteHeatHierarchy

/-! One original Wilson reconstruction carries all finite unmarked
comparison orders and a co-funded marked or matrix campaign. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatOriginal
open Filter Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Bank PhysicalNext.Repeat.Legato
open Next.Foundations WilsonMarkedIndependentPhysicalIntake WilsonLimitConstruction
open WilsonVacuumPreResetFiniteHeatTable WilsonVacuumPreResetFiniteHeatScale
open scoped Topology
variable {G:Gauge}

theorem funded (simple:G.Simple){ε:ℝ}(hε:0<ε)
    (P:FundedCompanySelection.Prediction G)(hP:FundedPredictionSupply.AllPrices (@P)):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T), P R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      ∀e:ℕ,∀ᶠm:ℕ in atTop,∃s B:ℝ,0<s ∧ 1 ≤ B ∧ ∀N p:ℕ,m ≤ N→
        table R.family.path.levels R.metals.O e N m (R.family.side m p) (rate R.family.path.levels m p) ∧
        PositiveAt R.family.path.levels R.metals.O e N m (R.family.side m p) s B:=by
  obtain ⟨v,winding⟩:=WilsonVacuumPreResetFiniteHeatHierarchy.original G
  obtain ⟨R,T,W,paid,hp,plateau,facts⟩:=FundedMarkedCoverRows.original.{u} simple hε v (@P) hP
  exact ⟨R,T,W,hp,plateau,facts,winding R simple facts.2.2.2.2.2.2.1 paid⟩

end YM.Integration.WilsonVacuumPreResetFiniteHeatOriginal
