import YM.Integration.WilsonOriginalFoldedMarkedScalar
import YM.Integration.WilsonVacuumPreResetDatedDeposit

/-! The true prior's funded scalar fold cancels for every marked test on its original conditional law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedMarkedIncome
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


theorem normalized (S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (M:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(proper:LocalRatio O)
    (P Q:PChart G f)(hp:shellK 2 P)(hq:shellK 2 Q){k:ℕ}
    (law:∀t<k,coeff t (Blue.flash P-Blue.flash Q)=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff t (Blue.flash P-Blue.flash Q))))
    (w:Ink (Active G F⊕Woods G c)):
    let K:=treeInverse G S F H 0
    let a:=shot S F M O P
    let b:=shot S F M O Q
    let A:=inside S F H M O P
    let B:=inside S F H M O Q
    ∃ (ua:IsUnit A)(ub:IsUnit B),
    Equal k (OriginalTwoChartMarkedWick.normalized (Wick (Woods G c) K (raiseE a*w)) A ua)
      (OriginalTwoChartMarkedWick.normalized (Wick (Woods G c) K (raiseE b*w)) B ub) :=by
  intro K a b A B
  have zero (D:PChart G f):constantCoeff (shot S F M O D)=0:=by
    rw [shot,loom,←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,
      flash_blank (pack_zero S proper),map_zero]
  have origin:constantCoeff (soil (U:=Woods G c) (shift P Q))=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,soil,coeff_map,shift,coeff_mk,if_pos rfl,map_zero]
  have unit (D:PChart G f):IsUnit (inside S F H M O D) :=by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [inside,Cameo.glaze_log K (zero D)]
    exact isUnit_one
  exact ⟨unit P,unit Q,WilsonOriginalFoldedMarkedScalar.cancel K (zero P) (zero Q) origin
    (shotJet S F M O P Q hp hq law) w (unit P) (unit Q)⟩

open PhysicalNext.Repeat.Legato FreeResolvent
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Bank Ticket Cosmos Polestar WilsonCoeffUV.Bank.Mosaic

theorem original (R:Run G)(simple:G.Simple)(N i p e:ℕ)(hi:i<N)(F:Forest (step R i p).ratio)
    (Z:SeriesA G){σ C:ℝ}(issued:Issued R N (i+1) e Z σ C)
    (w:Ink (Active G F⊕Woods G (coarse R i p))):
    let S:=step R i p
    let H:=upper R N i
    let M:=prediction R N i p
    let O:=ratio R
    let K:=treeInverse G S F H 0
    let P:=filed R N i p Z
    let Q:=covered R N i p
    let A:=inside S F H M O P
    let B:=inside S F H M O Q
    ∃(ua:IsUnit A)(ub:IsUnit B),
    Equal (3+e)
      (OriginalTwoChartMarkedWick.normalized (Wick (Woods G (coarse R i p)) K (raiseE (shot S F M O P)*w)) A ua)
      (OriginalTwoChartMarkedWick.normalized (Wick (Woods G (coarse R i p)) K (raiseE (shot S F M O Q)*w)) B ub) :=by
  intro S H M O K P Q A B
  have kp:(income R N i p).path=R.alloy.B.kin.path N (i+1):=(RunFormalChain.fromRun R).selected N p (i+1) hi
  have kb:(income R N i p).clip=((levels R).params (i+1)).clip:=(RunFormalChain.fromRun R).clips N p (i+1) hi
  have filedRows (t:ℕ)(ht:t<3+e)(l:ℕ):P t (l+1)=Q t (l+1):=by
    unfold P filed
    rw [kp,kb]
    exact issued.periodic t ht (fine R i p) l
  have hp:shellK 2 P:=WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _
  have hq:shellK 2 Q:=(emera_far (levels R) simple R.alloy.B.ratio hi (fine R i p)).1
  exact normalized S F H M O R.alloy.B.ratio P Q hp hq
    (fun t ht=>WilsonVacuumPreResetFoldedInlet.fieldIndependent P Q t hp (filedRows t ht)) w

end YM.Integration.WilsonOriginalFoldedMarkedIncome
