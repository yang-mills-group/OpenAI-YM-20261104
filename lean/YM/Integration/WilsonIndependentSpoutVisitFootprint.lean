import YM.Integration.WilsonIndependentMatchedOpeningExtent
/-! Extending the real visited menu by a nearest lattice center funds the same panel even when a test has no occupied cells. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutVisitFootprint
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedOpeningPorts (Port submitted)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (field seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open RegulatorIR.Cluster
open WilsonIndependentMatchedOpeningCensus (entry pace Sites)
open WilsonIndependentRawRosterWord (degree)
open RegulatorIR RegulatorIR.Motion WilsonCoeffUV.Mer.Patrol
open WilsonIndependentMatchedOpeningComposite (branch points)
open WilsonIndependentRawRosterBudget (span)

def anchor (ρ:Room):Cover:=fun j=>⌊ρ j⌋
theorem close (ρ:Room):dist ρ (slide 1 (anchor ρ))≤1:=by
  apply (dist_pi_le_iff (by norm_num:0≤(1:ℝ))).mpr
  intro j
  rw [slide_apply,one_mul,Real.dist_eq]
  unfold anchor
  have lower:=Int.floor_le (ρ j)
  have upper:=Int.lt_floor_add_one (ρ j)
  rw [abs_of_nonneg (by linarith)]
  linarith
variable {G:Gauge}{H:Hol G}{n h D k u e:ℕ}{p:h<D}{native:Labels.Frame G h}
  {T:SectionData native}{v:Rails h k u e}{E A K U:Credit}
variable (R:PhysicalNext.Repeat.Legato.Run G)(d:Fin (n+1)→ℕ)(φ:Fin (n+1)→Rarity D)
    (y:ℝ)(o:Fin (n+1)→ CellR)(X:Fin (n+1)→ CutsP H T p v E A K U)


abbrev Menu:=Option ((i:Fin (n+1))→Sites R d φ y o X i)

def sites (ρ:Room):(Menu R d φ y o X) → Fin (n+1) → Cover
  | none=>fun _=>anchor ρ
  | some z=>WilsonIndependentMatchedOpeningComposite.points R d φ y o X z

theorem original (ρ:Room)(live:∀i,0<pace X i)(b:Menu R d φ y o X):
    span ρ (sites R d φ y o X ρ b) (branch n id)≤
      ∑i,(dist ρ ((y/(pace X i)) • (o i).val) + ((φ i).radius+pace X i)/(pace X i)):=by
  cases b with
  | some z=>exact WilsonIndependentMatchedOpeningExtent.located R d φ y o X z ρ live
  | none=>
    rw [WilsonIndependentMatchedOpeningExtent.gather]
    apply Finset.sum_le_sum
    intro i _
    have rad:= (φ i).markG
    have ln:1 ≤ ((φ i).radius+pace X i)/(pace X i):=by
      apply (le_div_iff₀ (live i)).mpr;linarith
    exact (close ρ).trans (ln.trans (le_add_of_nonneg_left dist_nonneg))

end YM.Integration.WilsonIndependentSpoutVisitFootprint
