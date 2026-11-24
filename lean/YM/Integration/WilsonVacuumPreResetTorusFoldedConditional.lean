import YM.Integration.WilsonVacuumPreResetFoldedVacuumLog
import YM.Integration.WilsonOriginalSignedSamplerChart

/-! The deposited and folded quiet action on the entire original affine Gaussian slice. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusFoldedConditional
open Function Filter Finset Lattice RG Wilson Precision Tree Exterior FreeResolvent PowerSeries Matrix
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open scoped Classical BigOperators
variable {G:Gauge}{c f:Side}

private def shift (P Q:PChart G f): PowerSeries ℝ := mk fun t=>
  if t=0 then 0 else -MvPolynomial.eval 0 (coeff t (Blue.flash P-Blue.flash Q))

private theorem scrubbed (P:PChart G f)(t:ℕ) : coeff t (Blue.flash (scrub P)) =
    if t=0 then 0 else coeff t (Blue.flash P) := by
  by_cases h:t=0
  · subst t
    rw [if_pos rfl,coeff_zero_eq_constantCoeff_apply,flash_blank (show scrub P 0=0 by simp [scrub])]
  · simp only [Blue.flash,coeff_mk,scrub,if_neg h]

private theorem entered (P Q:PChart G f){k:ℕ}
    (law:∀t<k,coeff t (Blue.flash P-Blue.flash Q) =
      MvPolynomial.C (MvPolynomial.eval 0 (coeff t (Blue.flash P-Blue.flash Q)))) :
    ∀t<k,coeff t (Blue.flash (scrub P))-coeff t (Blue.flash (scrub Q))=
      -MvPolynomial.C (coeff t (shift P Q)) := by
  intro t ht
  rw [scrubbed,scrubbed,shift,coeff_mk]
  split_ifs with h
  · simp
  · simpa only [map_neg,neg_neg,map_sub] using law t ht

private theorem shotJet (S:StepData c f)(F:Forest S.ratio)
    (M:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)
    (P Q:PChart G f)(hp:shellK 2 P)(hq:shellK 2 Q){k:ℕ}
    (law:∀t<k,coeff t (Blue.flash P-Blue.flash Q)=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff t (Blue.flash P-Blue.flash Q)))) :
    Equal k (shot S F M O P) (shot S F M O Q+holdUp (Active G F) (soil (shift P Q))) := by
  intro t ht
  let C:=camber G (extractV G S F M)
  let V:=overM G S F
  have h:=congrArg (fun x:POL (Woods G f)=>cord V (cord C x)) (entered P Q law t ht)
  simp only [map_sub,map_neg,cord,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq] at h
  rw [shot,sterol S hp O,shot,sterol S hq O]
  simp only [map_add,map_sub,loom,coeff_map,soil,holdUp,holdUpPoly]
  change _ - _ - cord V (cord C _) = _ - _ - cord V (cord C _) +
    (MvPolynomial.rename (Sum.inr:Woods G c → Active G F ⊕ Woods G c))
      (MvPolynomial.C (coeff t (shift P Q)))
  rw [MvPolynomial.rename_C]
  change cord V (cord C _) - cord V (cord C _) = _ at h
  linear_combination -h

/-- Centering the original conditional vacuum logarithm removes exactly the scalar
left by the funded fold. Both held fields use the full covariance on the same forest. -/
theorem centered (S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (M:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(proper:LocalRatio O)
    (P Q:PChart G f)(hp:shellK 2 P)(hq:shellK 2 Q){k:ℕ}
    (law:∀t<k,coeff t (Blue.flash P-Blue.flash Q)=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff t (Blue.flash P-Blue.flash Q))))
    (t:ℕ)(ht:t<k)(x y:Lawn (Woods G c)):
    let A:=coeff t (logOf (inside S F H M O P))
    let B:=coeff t (logOf (inside S F H M O Q))
    MvPolynomial.eval x A-MvPolynomial.eval y A =
      MvPolynomial.eval x B-MvPolynomial.eval y B := by
  have zero (D:PChart G f):constantCoeff (shot S F M O D)=0:=by
    rw [shot,loom,←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,
      flash_blank (pack_zero S proper),map_zero]
  have origin:constantCoeff (soil (U:=Woods G c) (shift P Q))=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,soil,coeff_map,shift,coeff_mk,if_pos rfl,map_zero]
  have exactLog:=WilsonVacuumPreResetFoldedVacuumLog.conditional (treeInverse G S F H 0)
    (zero P) (zero Q) origin (shotJet S F M O P Q hp hq law) t ht
  intro A B
  have coefficient:A=B+MvPolynomial.C (coeff t (shift P Q)):=by
    simpa only [A,B,inside,map_add,soil,coeff_map] using exactLog
  rw [coefficient,map_add,map_add,MvPolynomial.eval_C,MvPolynomial.eval_C]
  abel

end YM.Integration.WilsonVacuumPreResetTorusFoldedConditional
