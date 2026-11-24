import YM.Integration.WilsonOriginalPublicRelativeGramSale

/-! Pay the amplification in the two-date frame conversion by the actual
original absolute pair at the physical nodes, independently of the K trial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramRough
open Filter Finset Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonOriginalPublicRelativeGramPins (matrix cutoff)
open WilsonOriginalPublicRelativeGramTransport (transition)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)} {I L:Type}[Fintype I][Fintype L](a:Axis)(h:ℕ)
    (J:ℝ→PhysMS.tower S)(basis:Module.Basis I ℂ ((Spin.comparator R.family.book).Field h))
    (r s:ℝ)(site:ℕ)(points:L→Fin 2→ Cover)(μ:L→ℂ)(Y:Bool→(ℕ×ℕ)→I→R.family.label h)
local notation "M" => matrix R F a (fun _:I=>h) J (fun i=>basis i) r s site points μ
local notation "C₀" => cutoff R a (fun _:I=>h) site points μ Y

theorem original (b:Bool→I→R.family.label h)
    (converges:∀t i,Tendsto (fun z=>Y t z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b t i)))
    (same:∀t i,S.project h (b t i)=J (cond t s r) h (basis i))
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(admitted:∀m,μ m≠0→Extraction.Order.grid R.family site (points m)∈generic 2)
    (cash:I→I→ℝ)(paid:∀ᶠ z:ℕ×ℕ in f.fuse,∀i j,‖C₀ true z i j‖≤cash i j)
    {K:ℝ}(positive:0≤K)(rank:IsUnit (M false).det)(reference:‖(M false)⁻¹‖≤K):
    ‖transition R h J basis r s‖≤K*(∑i,∑j,cash i j):=by
  have read (i j:I): ‖M true i j‖≤cash i j:=
    le_of_tendsto ((WilsonOriginalPublicRelativeGramPins.limit R F a (fun _:I=>h) J (fun i=>basis i)
      r s site points μ Y b converges same below admitted true i j).norm)
      ((paid.filter_mono below).mono fun _ atNode=>atNode i j)
  have whole:=WilsonOriginalPublicRelativeGramPanel.entry_bound cash read
  rw [←WilsonOriginalPublicRelativeGramTransport.original R F a h J basis r s site points μ rank]
  exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_right reference (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left whole positive))

end YM.Integration.WilsonOriginalPublicRelativeGramRough
