import YM.Integration.WilsonOriginalPublicRelativeGramCircuits
import YM.Integration.WilsonOriginalPublicRelativeGramTransport

/-! Signed two-date fees on the original nodes compare the actual public
change of basis to the compensated columns of the independently filed table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramSale
open Filter Finset Function Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open XSpace XSpace.Normalize XSpace.Rose
open WilsonOriginalPublicRelativeGramPins (matrix cutoff)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits)
open WilsonOriginalPublicRelativeGramTransport (transition)
open WilsonOriginalPublicRelativeGramJoined (fee)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G)(W:Initialize G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {ℓ:Ultrafilter (ℕ×ℕ)}{I L:Type}[Fintype I][Fintype L]
  (a:Axis)(h:ℕ)(J:ℝ→PhysMS.tower S)(basis:Module.Basis I ℂ ((Spin.comparator R.family.book).Field h))
  (r s:ℝ)(site:ℕ)(points:L→Fin 2→ Cover)(μ:L→ℂ)(Y:Bool→(ℕ×ℕ)→I→R.family.label h)
  (sale:Dated (L:=L) R W (fun _:I=>h))
local notation "M" => matrix R F a (fun _:I=>h) J (fun k=>basis k) r s site points μ
local notation "C₀" => cutoff R a (fun _:I=>h) site points μ Y
local notation "bank" => submitted R W (fun _:I=>h) sale
local notation "old" => deposits R W (fun _:I=>h) sale
local notation "field" => transition R h J basis r s

theorem original (b:Bool→I→R.family.label h)
    (converges:∀t i,Tendsto (fun z=>Y t z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b t i)))
    (same:∀t i,S.project h (b t i)=J (cond t s r) h (basis i))
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(admitted:∀m,μ m≠0→Extraction.Order.grid R.family site (points m)∈generic 2)
    (tuition rest:Bool→I→I→ℝ)(η:ℝ)(ep:0<η)
    (earned:∀ᶠ z:ℕ×ℕ in f.fuse,∀t i j,‖C₀ t z i j-bank t z i j‖≤tuition t i j ∧ old t z i j≤rest t i j)
    (rank:IsUnit (M false).det)(K price:ℝ)(reference:‖(M false)⁻¹‖≤K)
    (stable:K*max 0 (fee η (tuition false+rest false))≤1/2)
    (paid:2*K*(max 0 (fee η (tuition true+rest true))+max 0 (fee η (tuition false+rest false))*‖field‖)≤price):
    ∀ᶠ z:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),IsUnit (sale.frame false z).det ∧
      ‖field-(sale.frame false z)⁻¹*sale.frame true z‖≤price:=by
  have op:‖(M false)⁻¹‖*fee η (tuition false+rest false)≤1/2:=
    (mul_le_mul_of_nonneg_left (le_max_right 0 _) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right reference (le_max_left 0 _)).trans stable)
  have real:=WilsonOriginalPublicRelativeGramTransport.original R F a h J basis r s site points μ rank
  have quote:=WilsonOriginalPublicRelativeGramGrid.total R W F a (fun _:I=>h) J (fun k=>basis k) r s site points μ Y sale
    b converges same below admitted tuition rest η ep earned rank op
  filter_upwards [quote] with z hz
  rw [real] at hz
  refine ⟨hz.1,hz.2.trans (le_trans ?_ paid)⟩
  refine (mul_le_mul_of_nonneg_left (add_le_add (le_max_right 0 _) (mul_le_mul_of_nonneg_right (le_max_right 0 _) (norm_nonneg _))) (by positivity)).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (le_max_left 0 _) (mul_nonneg (le_max_left 0 _) (norm_nonneg _)))

end YM.Integration.WilsonOriginalPublicRelativeGramSale
