import YM.Integration.WilsonOriginalPublicRelativeGramPanel

/-! Entrywise control of the original measured matrix from its operator norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickNorms
open Finset
open scoped Classical BigOperators Matrix.Norms.Operator
theorem original {I:Type*}[Fintype I](M:Matrix I I ℂ):‖(fun i j:I=>M i j)‖≤‖M‖:=by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg M)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg M)).mpr
  intro j
  have one:‖M i j‖₊≤∑k:I,‖M i k‖₊:=Finset.single_le_sum (f:=fun k:I=>‖M i k‖₊) (fun _ _=>bot_le) (Finset.mem_univ j)
  have row:(∑k:I,‖M i k‖₊)≤Finset.univ.sup (fun t:I=>∑k:I,‖M t k‖₊):=
    Finset.le_sup (s:=Finset.univ) (f:=fun t:I=>∑k:I,‖M t k‖₊) (Finset.mem_univ i)
  rw [Matrix.linfty_opNorm_def]
  exact NNReal.coe_le_coe.mpr (one.trans row)

end YM.Integration.WilsonPhysicalStationMixedWickNorms
end
