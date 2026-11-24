import YM.Integration.WilsonLimitConstruction.FundedPacketWidthChain
import YM.Integration.WilsonLimitConstruction.FundedNeutralCostRun

/-! Genuine funding of both ends and all internal component widths in each
pre-period finite diagram. The original request portfolio is retained. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonLimitConstruction.FundedPacketWidthPrices
open Filter Lattice RG RG.Supply Precision Marker FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.CostProfile FullQLocal.PreRun.Profile
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open FundedNeutralCostRun
open scoped Topology

abbrev Diagrams (G : Gauge) := ∀ (s : Sheet G) (q : MapPrices) (C : NativeComponentRecipe.Choice s), ℕ→Diagram s q C
abbrev Ceilings (G : Gauge) := ∀ (s : Sheet G), MapPrices→NativeComponentRecipe.Choice s→ℕ→ProfileWidths

variable {G : Gauge}

def tariff {s : Sheet G} {q : MapPrices} {C : NativeComponentRecipe.Choice s}
    {D : Diagram s q C} (W : Allocation D) (i : ℕ) :=
  max |(W.input.width i)⁻¹| (max |(W.output.width i)⁻¹| |W.profileBill i|)

def augment (I : Inventory G) (D : Diagrams G) (H : Ceilings G) : Inventory G := fun s q C n =>
  { I s q C n with
    preRequest := fun i =>
      max (abs ((I s q C n).preRequest i)) (tariff (FundedPacketWidthChain.allocation (D s q C) (H s q C) n) i) }

variable {I : Inventory G} {D : Diagrams G} {H : Ceilings G} {R : Run G} (p : Purchase (augment I D H) R)

abbrev layout (n : ℕ) := FundedPacketWidthChain.allocation (D p.sheet p.quote p.choice) (H p.sheet p.quote p.choice) n

def original : Purchase I R where
  sheet := p.sheet
  quote := p.quote
  choice := p.choice
  lengths := p.lengths
  base := p.base
  original_sheet := p.original_sheet
  original_quote := p.original_quote
  components := p.components
  numbers := by
    refine ⟨p.numbers.extra_le,⟨p.numbers.numeric_paid.1,?_⟩,p.numbers.post_paid⟩
    intro n
    obtain ⟨a,h⟩ := p.numbers.numeric_paid.2 n
    refine ⟨a,fun m hm i hi => le_trans ?_ (h m hm i hi)⟩
    let row := I p.sheet p.quote p.choice n
    let price := tariff (layout p n) i
    change abs (max (abs ((row.widths.width i)⁻¹)) (abs (row.preRequest i))) ≤
      abs (max (abs ((row.widths.width i)⁻¹)) (abs (max (abs (row.preRequest i)) price)))
    rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg _)),abs_of_nonneg (le_max_of_le_left (abs_nonneg _)),
      abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    exact max_le_max_left _ (le_max_left _ _)

theorem register (n i : ℕ) :
    tariff (layout p n) i≤|Resources.numeric (augment I D H p.sheet p.quote p.choice) n i| := by
  exact (le_max_right _ _).trans ((le_abs_self _).trans ((le_max_right _ _).trans (le_abs_self _)))

theorem inside : ActualCountableWidthPayment.PaidWidths (fun n=>(layout p n).input) R.family.path.levels := by
  refine ⟨p.numbers.numeric_paid.1,?_⟩
  intro n
  obtain ⟨a,h⟩ := p.numbers.numeric_paid.2 n
  exact ⟨a,fun m hm i hi=>(le_max_left _ _).trans ((register p n i).trans (h m hm i hi))⟩

theorem outside : ActualCountableWidthPayment.PaidWidths (fun n=>(layout p n).output) R.family.path.levels := by
  refine ⟨p.numbers.numeric_paid.1,?_⟩
  intro n
  obtain ⟨a,h⟩ := p.numbers.numeric_paid.2 n
  exact ⟨a,fun m hm i hi=>(le_max_left _ _).trans ((le_max_right _ _).trans ((register p n i).trans (h m hm i hi)))⟩

def input_payment (n : ℕ) : WidthPayment R.family (layout p n).input :=
  ActualCountableWidthPayment.payment _ R.family (inside p) n

def output_payment (n : ℕ) : WidthPayment R.family (layout p n).output :=
  ActualCountableWidthPayment.payment _ R.family (outside p) n

theorem components (n : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ i, i≤R.family.path.levels.clock.J (m+1) →
    |(layout p n).profileBill i|≤1+Real.log (Real.log (R.family.path.levels.clock.hatBeta m)) := by
  obtain ⟨a,h⟩ := p.numbers.numeric_paid.2 n
  filter_upwards [eventually_ge_atTop a] with m hm i hi
  exact (le_max_right _ _).trans ((le_max_right _ _).trans ((register p n i).trans (h m hm i hi)))

theorem reciprocal (n : ℕ) : ∀ᶠ m : ℕ in atTop, ((layout p n).target R.family m)⁻¹ ≤
    1+Real.log (Real.log (R.family.path.levels.clock.hatBeta m)) := by
  let L := R.family.path.levels
  let W := layout p n
  obtain ⟨first,g⟩ := (outside p).2 n
  filter_upwards [eventually_ge_atTop first] with m hm
  let t := 1+Real.log (Real.log (L.clock.hatBeta m))
  have cash (i : ℕ) (hi : i≤L.clock.J (m+1)) : (W.output.width i)⁻¹≤t :=
    (le_abs_self _).trans (g m hm i hi)
  have a := cash (L.clock.J ((m-1)+1)) (L.fits.mono (by omega))
  have b := cash (L.clock.J (m-1)) (L.fits.mono (by omega))
  have pair : (W.output.pair R.family (m-1))⁻¹≤t := by
    change (min (W.output.width (L.clock.J ((m-1)+1))) (W.output.width (L.clock.J (m-1))))⁻¹ ≤ t
    rcases le_total (W.output.width (L.clock.J ((m-1)+1))) (W.output.width (L.clock.J (m-1))) with h|h
    · rw [min_eq_left h]
      exact a
    · rw [min_eq_right h]
      exact b
  change (min (W.output.pair R.family (m-1)) 1)⁻¹ ≤ t
  rcases le_total (W.output.pair R.family (m-1)) 1 with h|h
  · rw [min_eq_left h]
    exact pair
  · rw [min_eq_right h,inv_one]
    exact p.numbers.numeric_paid.1 m

theorem supported (hG : G.Simple) {V : Type} [DecidableEq V] [Fintype V] (J : Request V) (n : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ A : NumericSchedule R.family J,
      (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ)≤((layout p n).input.pair R.family m/2)/4 ∧
      (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ)≤(layout p n).target R.family m/4 := by
  filter_upwards [FundedPresoldPacketWidths.geometry R J hG (layout p n).input (input_payment p n),
    FundedNativePacketGeometry.eventually R hG J,reciprocal p n] with m first second bill
  intro A
  exact ⟨first A,FundedNativePacketGeometry.reserve (A.outputNorm m)
    (lt_min ((layout p n).output.pair_positive R.family (m-1)) zero_lt_one) (second A) bill⟩

theorem purchase (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (I : Inventory G) (D : Diagrams G) (H : Ceilings G)
    (prediction : FundedCompanySelection.Prediction G) (paid : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Nonempty (Purchase I R) ∧ Nonempty (Purchase (augment I D H) R) := by
  obtain ⟨R,T,W,hp,hc,hw,⟨p⟩⟩ := FundedNeutralCostRun.original.{u} hG hε (augment I D H) (@prediction) paid
  exact ⟨R,T,W,hp,hc,hw,⟨original p⟩,⟨p⟩⟩

end YM.Integration.WilsonLimitConstruction.FundedPacketWidthPrices
end
