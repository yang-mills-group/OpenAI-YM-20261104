import YM.Integration.WilsonOriginalPublicRelativeGramTransport
import YM.Integration.MeasuringFrameTransitionBound

/-! The actual two-date matrix on the full public quotient and its adjoint are
both priced before the upper planting date or either finite regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOptical
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramTransport (transition)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {I:Type}[Fintype I](h:ℕ)(J:ℝ→PhysMS.tower S)
  (basis:Module.Basis I ℂ ((Spin.comparator R.family.book).Field h))

theorem compose (r s t:ℝ):
    transition R h J basis r s * transition R h J basis s t=transition R h J basis r t:=by
  ext i j
  let form := (basis.coord i).comp ((J r h).symm.toLinearMap.comp (J s h).toLinearMap)
  have main:=congrArg (fun x=>form x) (basis.sum_repr ((J s h).symm (J t h (basis j))))
  simp only [map_sum,map_smul] at main
  rw [Matrix.mul_apply]
  calc
    _=∑k,basis.repr ((J s h).symm (J t h (basis j))) k • form (basis k):=
      Finset.sum_congr rfl fun k _=>mul_comm _ _
    _=form ((J s h).symm (J t h (basis j))):=main
    _=_:=by
      change basis.repr ((J r h).symm (J s h ((J s h).symm (J t h (basis j))))) i=_
      rw [LinearEquiv.apply_symm_apply]; rfl

variable [DecidableEq I]

omit [Fintype I] in
theorem same (r:ℝ):transition R h J basis r r=1:=by
  ext i j
  simp [transition,Module.Basis.repr_self,Matrix.one_apply,Finsupp.single_apply,eq_comm]

theorem original (leading:PhysMS.Leading F J):
    ∃ (C:ℝ)(k:ℕ),0<C ∧ ∀ᶠ t in trail,∀E:ℝ,1≤E →
      ‖transition R h J basis (t/E) t‖≤C*E^k ∧
      ‖(transition R h J basis (t/E) t)ᴴ‖≤C*E^k:=by
  obtain ⟨B,k,high,paid⟩:=MeasuringFrameTransitionBound.bound F h J leading
  let toll (i j:I):ℝ:=‖(basis.coord i).toContinuousLinearMap‖*B*‖basis j‖
  let C:=1+∑i,∑j,toll i j
  have nn (i j:I):0≤toll i j:=by dsimp [toll]; positivity
  have low:0<C:=by dsimp [C]; positivity
  refine ⟨C,k,low,?_⟩
  filter_upwards [paid] with t price
  intro E pos
  have entry (i j:I):‖transition R h J basis (t/E) t i j‖≤toll i j*E^k:=by
    refine ((basis.coord i).toContinuousLinearMap.le_opNorm _).trans ?_
    have b:=mul_le_mul_of_nonneg_left (price E pos (basis j)) (norm_nonneg (basis.coord i).toContinuousLinearMap)
    exact b.trans_eq (by dsimp [toll]; ring)
  have bound: (∑i,∑j,toll i j*E^k)≤C*E^k:=by
    simp_rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
  refine ⟨(WilsonOriginalPublicRelativeGramPanel.entry_bound _ entry).trans bound,?_⟩
  calc
    _ ≤ ∑i,∑j,toll j i*E^k:=WilsonOriginalPublicRelativeGramPanel.entry_bound _ fun i j=>by
      simpa [Matrix.conjTranspose_apply] using entry j i
    _ ≤ _:=by rwa [Finset.sum_comm]

end YM.Integration.WilsonOriginalPublicRelativeGramOptical
