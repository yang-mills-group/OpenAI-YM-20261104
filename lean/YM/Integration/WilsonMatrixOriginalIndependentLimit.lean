import YM.Integration.WilsonMatrixOriginalIndependentForest

/-! Fix the complete vector of independent grade-four coefficients before either finite regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentLimit
open Filter Function Lattice Labels RG RG12 RG17 Spec Wilson MS.Local.Physical MS.Menus FVA2
open PhysicalNext.Repeat.Legato Next.Rank.Price WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns WilsonMatrixTicketLanesRegulatorColumn
open WilsonMatrixOriginalIndependentForest
open RGComparison.Core16.Astage
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F)

/-- The registered earlier coefficient of the very filed upper field is its original window shift. -/
theorem filed (r:ℝ) (w:R.family.label 4) (N p:ℕ) (age:R.family.ref 4≤L.level r) (live:L.level r≤N) :
    entry R 4 (L.level r) N p (atRef L 4 r (N,p) w)=L.shift 4 r w := by
  let m:=L.level r
  let A:=RG12.charts R.family F.room.cutoff 4 m (N,p)
  let a:ℂ:=(R.family.S.a m^4:ℝ)
  have ha:a≠0:=Complex.ofReal_ne_zero.mpr (pow_ne_zero 4 (R.family.S.a_pos m).ne')
  have h:=attached R F L 4 m N p age live (atRef L 4 r (N,p) w)
  change a • A.symm (entry R 4 m N p (atRef L 4 r (N,p) w)) = a • A.symm (L.shift 4 r w) at h
  have h' := congrArg (fun y:R.family.label 4=>a⁻¹ • y) h
  simp only [smul_smul,inv_mul_cancel₀ ha,one_smul] at h'
  exact A.symm.injective h'

def fixed (τ:ℕ→ℝ) (r:ℝ) (w:R.family.label 4) : Glyph B 4→ℂ :=
  weights (warehouse R) B 4 ((R.family.labels.level 4).scaled (τ (L.level r)) (L.shift 4 r w))

def Climate (U:Ultrafilter (ℕ×ℕ)) (τ:ℕ→ℝ) : Prop :=
  ∀m,0<τ m ∧ τ m≤2 ∧ Tendsto (fun z:ℕ×ℕ=>shrink R.family m z.1 z.2) (U:Filter (ℕ×ℕ)) (𝓝 (τ m))

/-- One temperature sequence is chosen before the radius, laboratory fields, coefficients or accuracy. -/
theorem selected (U:Ultrafilter (ℕ×ℕ)) (hu:(U:Filter (ℕ×ℕ))≤L.lens) :
    ∃τ:ℕ→ℝ,Climate R U τ ∧
    ∀(r:ℝ)(w:R.family.label 4),R.family.ref 4≤L.level r→
      Tendsto (fun z:ℕ×ℕ=>coefficient R B (L.level r) z.1 z.2 (atRef L 4 r z w))
        (U:Filter (ℕ×ℕ)) (𝓝 (fixed R B F L τ r w)) := by
  have sub:=hu.trans L.certified
  obtain ⟨τ,hτ⟩:=WilsonMatrixTicketLanesReportedMaster.units R (f:=f) U sub
  refine ⟨τ,hτ,?_⟩
  intro r w age
  let m:=L.level r
  let x:=L.shift 4 r w
  have raw : Tendsto (fun z:ℕ×ℕ=>(R.family.labels.level 4).scaled (shrink R.family m z.1 z.2) x)
    (U:Filter (ℕ×ℕ)) (𝓝 ((R.family.labels.level 4).scaled (τ m) x)) := by
    apply tendsto_pi_nhds.mpr; intro i
    simp only [Frame.scaled_apply]
    exact ((Complex.continuous_ofReal.tendsto _).comp ((hτ m).2.2.pow _)).mul_const _
  have spectral := ((weights (warehouse R) B 4).continuous_of_finiteDimensional.tendsto _).comp raw
  apply spectral.congr'
  filter_upwards [((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono sub] with z live
  change _=weights (warehouse R) B 4 ((R.family.labels.level 4).scaled (shrink R.family m z.1 z.2)
    (entry R 4 (L.level r) z.1 z.2 (atRef L 4 r z w)))
  rw [filed R F L r w z.1 z.2 age live];rfl

/-- The fixed independent arm evaluates to the exact issued continuum physical field on this same run. -/
theorem measured (simple:G.Simple) (U:Ultrafilter (ℕ×ℕ)) (hu:(U:Filter (ℕ×ℕ))≤L.lens) :
    ∃(τ:ℕ→ℝ)(A:Axle.TransferLimit R.family R.makes U),Climate R U τ ∧
    ∀(r:ℝ)(w:R.family.label 4),R.family.ref 4≤L.level r→
      Tendsto (fun z:ℕ×ℕ=>coefficient R B (L.level r) z.1 z.2 (atRef L 4 r z w))
        (U:Filter (ℕ×ℕ)) (𝓝 (fixed R B F L τ r w)) ∧
      (∑q:Glyph B 4,fixed R B F L τ r w q •
        Axle.full F 4 A (L.level r) (column (warehouse R) B 4 q))=master L 4 r w := by
  obtain ⟨τ,hτ,limit⟩:=selected R B F L U hu
  obtain ⟨A⟩:=Axle.option R.makes U (hu.trans L.certified)
  refine ⟨τ,A,hτ,?_⟩
  intro r w age
  refine ⟨limit r w age,?_⟩
  let y:R.family.label 4 := (R.family.labels.level 4).scaled (τ (L.level r)) (L.shift 4 r w)
  let E:=Axle.full F 4 A (L.level r)
  have eval:E y=master L 4 r w :=
    WilsonMatrixTicketLanesReportedMaster.measured R F L U (hu.trans L.certified) hu A τ (fun m=>(hτ m).2.2) 4 r w age
  calc
    _=E y := ((congrArg E (resolution (warehouse R) B simple y)).trans
      ((map_sum E _ _).trans (Finset.sum_congr rfl (fun q _=>E.map_smul _ _)))).symm
    _=_ := eval

end YM.Integration.WilsonMatrixOriginalIndependentLimit
