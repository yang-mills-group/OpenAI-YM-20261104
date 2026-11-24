import YM.Integration.WilsonVacuumPreResetTorusFoldedConditional
import YM.Integration.OriginalTwoChartMarkedWick

/-! A refiled scalar cancels through every incoming marked insertion on the same conditional finite Wick slice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedMarkedScalar
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


theorem cofactors {U V:Type}[Fintype U][Fintype V]
    (K:Matrix U U ℝ){k:ℕ}{a b:Ink (U⊕V)}{s:Ink V}
    (ha:constantCoeff a=0)(hb:constantCoeff b=0)(hs:constantCoeff s=0)
    (eq:Equal k a (b+holdUp U s))(w:Ink (U⊕V)):
    Equal k (Wick V K (raiseE a*w)) (Wick V K (raiseE b*w)*raiseE s) := by
  have up:constantCoeff (holdUp U s)=0:=by
    rw [← coeff_zero_eq_constantCoeff_apply,holdUp,coeff_map,coeff_zero_eq_constantCoeff_apply,hs,map_zero]
  have h0:constantCoeff (b+holdUp U s)=0:=by rw [map_add,hb,up,zero_add]
  have ex:Equal k (raiseE a) (raiseE (b+holdUp U s)):=substitute ha h0 eq _
  rw [raise_add hb up,← raise_map (holdUp U) (by simp [holdUp]) hs] at ex
  have joined:=ex.mul (Equal.refl w k)
  rw [mul_right_comm (raiseE b) (holdUp U (raiseE s)) w] at joined
  rw [← W_param]
  intro j hj
  simp only [Wick,projectZero,coeff_map,fullB,blur,overlay_apply,joined j hj]

theorem cancel {U V:Type}[Fintype U][Fintype V]
    (K:Matrix U U ℝ){k:ℕ}{a b:Ink (U⊕V)}{s:Ink V}
    (ha:constantCoeff a=0)(hb:constantCoeff b=0)(hs:constantCoeff s=0)
    (eq:Equal k a (b+holdUp U s))(w:Ink (U⊕V)):
    let A:=Wick V K (raiseE a)
    let B:=Wick V K (raiseE b)
    ∀(ua:IsUnit A)(ub:IsUnit B),
    Equal k (OriginalTwoChartMarkedWick.normalized (Wick V K (raiseE a*w)) A ua)
      (OriginalTwoChartMarkedWick.normalized (Wick V K (raiseE b*w)) B ub) :=by
  intro A B ua ub
  let C:=Wick V K (raiseE a*w)
  let D:=Wick V K (raiseE b*w)
  have occ:Equal k C (D*raiseE s):=cofactors K ha hb hs eq w
  have vac:Equal k A (B*raiseE s):=by
    simpa only [mul_one] using cofactors K ha hb hs eq 1
  have populated:=occ.mul (Equal.refl B k)
  rw [mul_right_comm D (raiseE s) B,mul_assoc] at populated
  have crossed:=populated.trans ((Equal.refl D k).mul vac.symm)
  have paid:=crossed.mul (Equal.refl ((↑(ua.unit⁻¹):Ink V)*(↑(ub.unit⁻¹):Ink V)) k)
  have restoreA:A*(↑(ua.unit⁻¹):Ink V)=1:=by calc
    _ = (↑ua.unit:Ink V)*↑(ua.unit⁻¹) := congrArg (· * (↑(ua.unit⁻¹):Ink V)) ua.unit_spec.symm
    _ = _ := by simp
  have restoreB:B*(↑(ub.unit⁻¹):Ink V)=1:=by calc
    _ = (↑ub.unit:Ink V)*↑(ub.unit⁻¹) := congrArg (· * (↑(ub.unit⁻¹):Ink V)) ub.unit_spec.symm
    _ = _ := by simp
  have ca:C*B*((↑(ua.unit⁻¹):Ink V)*↑(ub.unit⁻¹))=
      OriginalTwoChartMarkedWick.normalized C A ua:=by
    unfold OriginalTwoChartMarkedWick.normalized
    calc
      _ = (C*(↑(ua.unit⁻¹):Ink V))*(B*↑(ub.unit⁻¹)):= by ring
      _ = _ := by rw [restoreB,mul_one]
  have cb:D*A*((↑(ua.unit⁻¹):Ink V)*↑(ub.unit⁻¹))=
      OriginalTwoChartMarkedWick.normalized D B ub:=by
    unfold OriginalTwoChartMarkedWick.normalized
    calc
      _ = (D*(↑(ub.unit⁻¹):Ink V))*(A*↑(ua.unit⁻¹)):= by ring
      _ = _ := by rw [restoreA,mul_one]
  rwa [ca,cb] at paid

end YM.Integration.WilsonOriginalFoldedMarkedScalar
