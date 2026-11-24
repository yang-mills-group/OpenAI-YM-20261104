import YM.Integration.WilsonOriginalPublicRelativeGramPanel

/-! The observed relative matrix has one price on the elected physical extraction.
Both original slot charges enter at their actual dates before summation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramJoined
open Filter Finset Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonOriginalPublicRelativeGramPanel
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{ℓ:Ultrafilter (ℕ×ℕ)}
  (arch:Trace.Terrace.Arch R.family)(bliss:Trace.Pilot.Bliss F ℓ arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
  {I:Type}[Fintype I][DecidableEq I](a:Axis)(d:I→ℕ)(w:(i:I)→(Spin.comparator R.family.book).Field (d i))
  (φ:I→Test 1)(supports:∀i,∀x∈tsupport (φ i),Points.allAbove a 0 x)
local notation "O" => before R F arch J level shift a d w φ
local notation "M" => measured R J a d w φ supports
local notation "Mat" => Matrix I I ℂ

def fee (η:ℝ)(σ:I→I→ℝ):ℝ:=∑i,∑j,(η+σ i j)

private theorem invoice (X T Z:Mat)(η:ℝ)(σ:I→I→ℝ)
    (physical:∀i j,‖T i j-X i j‖ ≤ η)(signed:∀i j,‖T i j-Z i j‖ ≤ σ i j):
    ‖X-Z‖ ≤ fee η σ:=by
  apply entry_bound
  intro i j
  change ‖X i j-Z i j‖ ≤ η+σ i j
  calc
    _ ≤ ‖X i j-T i j‖+‖T i j-Z i j‖ := by simpa only [dist_eq_norm] using dist_triangle (X i j) (T i j) (Z i j)
    _ ≤ _ := add_le_add ((norm_sub_rev _ _).le.trans (physical i j)) (signed i j)

include bliss in
theorem original (r s:ℝ)(atR:∀i,R.family.ref (d i) ≤ level r)(atS:∀i,R.family.ref (d i) ≤ level s)
    (B Y A:(ℕ×ℕ)→Mat)(σ τ:I→I→ℝ)(η:ℝ)(ep:0<η)
    (signed:∀ᶠ z:ℕ×ℕ in f.fuse,∀i j,
       ‖O r r z i j-((B z)ᴴ*A z*B z) i j‖ ≤ σ i j ∧
       ‖O r s z i j-((B z)ᴴ*A z*Y z) i j‖ ≤ τ i j)
    (rank:IsUnit (M r r).det)(small:‖(M r r)⁻¹‖*fee η σ ≤ 1/2):
    ∀ᶠ z:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)), IsUnit (B z).det ∧
      ‖(M r r)⁻¹*M r s-(B z)⁻¹*Y z‖ ≤
        2*‖(M r r)⁻¹‖*(fee η τ+fee η σ*‖(M r r)⁻¹*M r s‖):=by
  have hrr:=WilsonOriginalPublicRelativeGramPanel.original R F arch bliss J level shift a d w φ supports
    r r atR atR η ep
  have hrs:=WilsonOriginalPublicRelativeGramPanel.original R F arch bliss J level shift a d w φ supports
    r s atR atS η ep
  filter_upwards [hrr,hrs,signed.filter_mono bliss.lies] with z rr rs hz
  exact WilsonOriginalPublicRelativeGramInverse.original _ _ _ _ _ rank _ _
    (invoice _ _ _ η σ rr fun i j=>(hz i j).1)
    (invoice _ _ _ η τ rs fun i j=>(hz i j).2) small

end YM.Integration.WilsonOriginalPublicRelativeGramJoined
