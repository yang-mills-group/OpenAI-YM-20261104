import YM.RegulatorIR.Clocks.Reprice
import YM.Comparison.RG02.Adjacent.Caliber
import YM.WilsonCoeffUV.Step.Rebase

/-! The actual inverse-temperature chart and the formal vacuum recursion give the same inverse series. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramRealInverseClock
open Function Filter Set Finset PowerSeries Comparison.RG02 Comparison.RG02.Adjacent
open RegulatorIR RegulatorIR.Prim WilsonCoeffUV.Blue PertExtension.Series
open scoped Topology BigOperators Classical ContDiff

private theorem identity : tale (id:ℝ→ℝ)=X:=by
  change tale (fun t:ℝ=>t)=X
  simpa using (Script.dictates (contDiffAt_id.pow 1) (Script.predicts_pow 1))

theorem entry (K:UnitCost):tale K.enter=tale K.rating * X:=by
  change tale ((id:ℝ→ℝ) * K.rating)=_
  rw [tale_mul contDiffAt_id (K.smooth.of_le le_top),identity,mul_comm]

private theorem positive (K:UnitCost):Tendsto K.enter Tested.germ Tested.germ:=by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨K.roots.mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin,K.bright.filter_mono nhdsWithin_le_nhds] with t ht h
  exact mul_pos ht h

private theorem direct (C:Caliber)(r:ℕ):tale (C.direct r).rating=pace (tale (C.tariff r)):=by
  let A:=C.direct r
  let f:=tale (C.tariff r)
  let g:=tale A.rating
  have hf:constantCoeff f=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply,tale_base,C.zero_tariff]
  have hg:constantCoeff g=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply,tale_base,A.origin]
  have equation: C.tariff r * (A.rating*A.rating)=ᶠ[𝓝 0] fun _=>1:=by
    filter_upwards [C.rates r] with t ht
    change C.tariff r t * ((Real.sqrt (C.tariff r t))⁻¹*(Real.sqrt (C.tariff r t))⁻¹)=1
    have root:=Real.sq_sqrt ht.le
    field_simp [ne_of_gt (Real.sqrt_pos.2 ht)]
    nlinarith
  have physical: f*(g*g)=1:=by
    have h:=tale_eq contDiffAt_const equation
    have smooth:ContDiffAt ℝ ∞ (A.rating*A.rating) 0:=(A.smooth.mul A.smooth).of_le le_top
    rw [tale_mul ((C.smooth r).contDiffAt.of_le le_top) smooth,
      tale_mul (A.smooth.of_le le_top) (A.smooth.of_le le_top),tale_const,map_one] at h
    exact h
  have ne:f≠0:=by intro h; simp [h] at hf
  have square:g^2=(pace f)^2:=by
    apply mul_left_cancel₀ ne
    rw [pace_tax hf,pow_two,physical]
  have vanish:(g-pace f)*(g+pace f)=0:=by calc
    _=g^2-(pace f)^2:=by ring
    _=0:=sub_eq_zero.mpr square
  rcases mul_eq_zero.mp vanish with h|h
  · exact sub_eq_zero.mp h
  · have zero:=congrArg (constantCoeff (R:=ℝ)) h
    rw [map_add,hg,pace_cc hf,map_zero] at zero
    norm_num at zero

theorem original (C:Caliber)(r:ℕ):tale (C.back r).rating=back (tale (C.tariff r)):=by
  let K:=C.direct r
  let B:=C.back r
  let f:=tale (C.tariff r)
  have hf:constantCoeff f=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply,tale_base,C.zero_tariff]
  have E:tale K.enter=oldG f:=by rw [entry,direct]; rfl
  have origin:coeff 0 (tale B.enter)=0:=by rw [tale_base,B.borne]
  have scripted:=Clocks.Outlook.tilted (Script.actual (K.here.of_le le_top))
    (Script.actual (B.here.of_le le_top)) origin (positive B)
  have wired:tale (K.enter ∘ B.enter)=(tale K.enter).subst (tale B.enter):=
    Script.dictates ((by rw [B.borne]; exact K.here.of_le le_top :
      ContDiffAt ℝ ∞ K.enter (B.enter 0)).comp _ (B.here.of_le le_top)) scripted
  have actual:(oldG f).subst (tale B.enter)=X:=by
    have h:(K.enter ∘ B.enter)=ᶠ[𝓝 0] id:=K.rightInverse.stairs
    rw [←E,←wired,tale_eq contDiffAt_id h,identity]
  have left:HasSubst (oldG f):=HasSubst.of_constantCoeff_zero' (cc_old f)
  have right:HasSubst (tale B.enter):=HasSubst.of_constantCoeff_zero' (by
    rw [←coeff_zero_eq_constantCoeff_apply,origin])
  have same:tale B.enter=freshG f:=by
    have h:=subst_comp_subst_apply left right (freshG f)
    rw [reverse_left hf,actual,X_subst] at h
    rwa [subst_X right] at h
  apply mul_right_cancel₀ (b:=X) X_ne_zero
  rw [←entry,fresh_back,same]

end YM.Integration.WilsonPositionProgramRealInverseClock
end
