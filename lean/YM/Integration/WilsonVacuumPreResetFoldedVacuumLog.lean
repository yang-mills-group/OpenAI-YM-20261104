import YM.Integration.WilsonVacuumPreResetFoldedInlet
import YM.WilsonCoeffUV.Kinetic.PerturbedIntegral

/-! Scalar changes of a finite fine-action jet through the original conditional Wick logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFoldedVacuumLog
open Finset PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open scoped BigOperators Classical

private theorem power {T:Type*}[CommRing T]{k:ℕ}{f g:PowerSeries T}
    (h:Equal k f g)(n:ℕ) : Equal k (f^n) (g^n) := by
  induction n with
  | zero => simp only [pow_zero]; exact Equal.refl (1:PowerSeries T) k
  | succ n ih => simpa only [pow_succ] using ih.mul h

private theorem substitute {T:Type*}[CommRing T]{k:ℕ}{f g:PowerSeries T}
    (hf:constantCoeff f=0)(hg:constantCoeff g=0)(h:Equal k f g)(d:PowerSeries T):
    Equal k (subst f d) (subst g d) := by
  have read {v:PowerSeries T}(hv:constantCoeff v=0) :
      subst v d = edit C hv d := by
    let M:PowerSeries T →+* PowerSeries T :=
      (substAlgHom (HasSubst.of_constantCoeff_zero' hv)).toRingHom
    have hx:M X=v:=substAlgHom_X _
    have H:M=edit C hv:=serial_ext (by rw [hx,hv])
      (fun i=>by rw [edit_C]; change substAlgHom _ _=_; rw [coe_substAlgHom]; exact PowerSeries.subst_C i)
      (by rw [edit_X,hx])
    rw [←H]
    exact congr_fun (coe_substAlgHom (HasSubst.of_constantCoeff_zero' hv)).symm d
  rw [read hf,read hg]
  intro i hi
  rw [edit_coeff C hf d hi,edit_coeff C hg d hi,map_sum,map_sum]
  exact sum_congr rfl fun j _ => ((Equal.refl (C (coeff j d)) k).mul (power h j)) i hi

private theorem logJet {T:Type*}[CommRing T][Algebra ℚ T]{k:ℕ}{f g:PowerSeries T}
    (hf:constantCoeff f=1)(hg:constantCoeff g=1)(h:Equal k f g):
    Equal k (logOf f) (logOf g) := by
  apply substitute (by simp only [map_sub,map_one,hf,sub_self]) (by simp only [map_sub,map_one,hg,sub_self])
  intro i hi
  simp only [map_sub,h i hi]

/-- A scalar from the original fine action is added to the conditional log at the
same coupling grades. All contractions use the same covariance and retained fields. -/
theorem conditional {U V:Type}[Fintype U][Fintype V]
    (K:Matrix U U ℝ){k:ℕ}{a b:Ink (U⊕V)}{s:Ink V}
    (ha:constantCoeff a=0)(hb:constantCoeff b=0)(hs:constantCoeff s=0)
    (eq:Equal k a (b+holdUp U s)):
    Equal k (logOf (Wick V K (raiseE a))) (logOf (Wick V K (raiseE b))+s) := by
  have up:constantCoeff (holdUp U s)=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,holdUp,coeff_map,coeff_zero_eq_constantCoeff_apply,hs,map_zero]
  have h0:constantCoeff (b+holdUp U s)=0:=by rw [map_add,hb,up,zero_add]
  have ex:Equal k (raiseE a) (raiseE (b+holdUp U s)):=substitute ha h0 eq _
  have integral:Equal k (Wick V K (raiseE a)) (Wick V K (raiseE (b+holdUp U s))):=by
    intro i hi
    simp only [Wick,projectZero,coeff_map,fullB,blur,overlay_apply,ex i hi]
  have mass:=Cameo.glaze_log K hb
  have z:=logJet (Cameo.glaze_log K ha) (Cameo.glaze_log K h0) integral
  rw [raise_add hb up,←raise_map (holdUp U) (by simp [holdUp]) hs,W_param,
    mul_comm (Wick V K (raiseE b)),Cameo.log_health mass hs,add_comm s] at z
  exact z

end YM.Integration.WilsonVacuumPreResetFoldedVacuumLog
