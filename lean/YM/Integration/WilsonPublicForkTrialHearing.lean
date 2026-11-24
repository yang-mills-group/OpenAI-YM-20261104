import YM.Integration.WilsonOriginalTwoFlatTelescope

/-! Both comparisons are evaluated using one chronological ordinary source on the original
quiet. Previously occupied nonconstant fields and their scalar deposits belong to that source. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkTrialHearing
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels OPE Bid Cells
open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per u v c K:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)

theorem fixed (uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)(kn:K ≤ N)(Y:Cut C N per)(hc:Continuous Y)
    (M:∀i:ℕ,(X i)→ℂ)(paid:∀i,v ≤ i → i ≤ K → Integrable (numerator R N per i (M i)) (prior G _))
    (I:ℂ):
    let lowerTop := uv.trans (vc.trans ck)
    let contact:=numerator R N per c (M c)
    let finish:=numerator R N per v (M v)
    ‖reading R (N:=N) (credit C N per 0 Y u (lowerTop.trans kn)) u le_rfl-I‖  ≤ 
      entrance R Y lowerTop kn M+
      (∑i∈Ico c K,‖feeAt R N per u M i‖)+
      ‖reading R (N:=N) contact u (uv.trans vc)-reading R (N:=N) contact v vc‖+
      (∑i∈Ico v c,‖feeAt R N per v M i‖)+
      ‖reading R (N:=N) finish v le_rfl-I‖:=by
  dsimp only
  let physical:=reading R (N:=N) (credit C N per 0 Y K kn) u (uv.trans (vc.trans ck))
  let upper:=reading R (N:=N) (numerator R N per K (M K)) u (uv.trans (vc.trans ck))
  let first:=reading R (N:=N) (numerator R N per c (M c)) u (uv.trans vc)
  let second:=reading R (N:=N) (numerator R N per c (M c)) v vc
  let last:=reading R (N:=N) (numerator R N per v (M v)) v le_rfl
  have own:reading R (N:=N) (credit C N per 0 Y u ((uv.trans (vc.trans ck)).trans kn)) u le_rfl=physical:=by
    dsimp only [physical,reading];rw [gust_base,cutoff R kn (uv.trans (vc.trans ck)) Y hc]
  have hi:‖upper-first‖ ≤ ∑i∈Ico c K,‖feeAt R N per u M i‖:=by
    dsimp only [upper,first]
    rw [interval R (uv.trans vc) ck kn M (fun i ci ik=>paid i (vc.trans ci) ik)]
    exact norm_sum_le ..
  have lo:‖second-last‖ ≤ ∑i∈Ico v c,‖feeAt R N per v M i‖:=by
    dsimp only [second,last]
    rw [interval R le_rfl vc (ck.trans kn) M (fun i vi ic=>paid i vi (ic.trans ck))]
    exact norm_sum_le ..
  rw [own]
  have route:physical-I=(physical-upper)+(upper-first)+(first-second)+(second-last)+(last-I):=by abel
  rw [route]
  have e₁:‖(physical-upper)+(upper-first)‖ ≤ entrance R Y (uv.trans (vc.trans ck)) kn M+
      ∑i∈Ico c K,‖feeAt R N per u M i‖:=(norm_add_le _ _).trans (add_le_add le_rfl hi)
  have e₂:‖(physical-upper)+(upper-first)+(first-second)‖ ≤
      (entrance R Y (uv.trans (vc.trans ck)) kn M+∑i∈Ico c K,‖feeAt R N per u M i‖)+‖first-second‖:=
    (norm_add_le _ _).trans (add_le_add e₁ le_rfl)
  have e₃:= (norm_add_le ((physical-upper)+(upper-first)+(first-second)) (second-last)).trans (add_le_add e₂ lo)
  exact (norm_add_le _ _).trans (add_le_add e₃ le_rfl)

end YM.Integration.WilsonPublicForkTrialHearing
