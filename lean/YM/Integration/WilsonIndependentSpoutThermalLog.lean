import YM.Integration.WilsonIndependentSpoutThermalChange
import YM.Integration.WilsonIndependentFittedRelativeClock

/-! The normalization commutes with the reported coupling substitution.
Pure vacuum scalars remain constant in every retained link. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutThermalLog
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {R S:Type*}[CommRing R][CommRing S]

private theorem floor₀ (f:PowerSeries R→+*PowerSeries S)(h:constantCoeff (f X)=0)
    {x:PowerSeries R}(hx:constantCoeff x=0):constantCoeff (f x)=0:=
  X_dvd_iff.mp ((X_dvd_iff.mpr h).trans (map_dvd f (X_dvd_iff.mpr hx)))

theorem floor₁ (f:PowerSeries R→+*PowerSeries S)(h:constantCoeff (f X)=0)
    {x:PowerSeries R}(hx:constantCoeff x=1):constantCoeff (f x)=1:=by
  have a:=floor₀ f h (x:=x-1) (by rw [map_sub,hx,map_one,sub_self])
  rw [map_sub,map_one,map_sub,map_one] at a
  exact sub_eq_zero.mp a

theorem log_map [Algebra ℚ R][Algebra ℚ S][IsAddTorsionFree R][IsAddTorsionFree S](f:PowerSeries R→+*PowerSeries S)
    (h:constantCoeff (f X)=0){x:PowerSeries R}(hx:constantCoeff x=1):
    f (logOf x)=logOf (f x):=by
  apply raise_inj (floor₀ f h (constantCoeff_logOf hx)) (constantCoeff_logOf (floor₁ f h hx))
  rw [←raise_map f h (constantCoeff_logOf hx),raising_log hx,raising_log (floor₁ f h hx)]

theorem log_product {U:Type}(p q:Ink U)(hp:constantCoeff p=1)(hq:constantCoeff q=1):
    logOf (p*q)=logOf p+logOf q:=by
  conv_lhs=> rw [←raising_log hp]
  exact Blue.Cameo.log_health hq (constantCoeff_logOf hp)

theorem cash {U:Type}(A B:Cost):redo A (soil (U:=U) B)=soil (Bank.reel A B):=by
  let P:=(redo (U:=U) A).comp soil
  let Q:=(soil (U:=U)).comp (Bank.reel A)
  have he:P X=soil A*X:=by simp [P,soil,redo_X]
  have ht:Q X=P X:=by rw [RingHom.comp_apply,reel_X,map_mul,he,soil,map_X]
  have same:P=Q:=by
    apply serial_ext (by rw [he];simp) _ ht.symm
    intro i
    unfold P Q
    rw [RingHom.comp_apply,RingHom.comp_apply,reel_C]
    rw [show soil (U:=U) (C i)=realS i by rw [soil,map_C];rfl,redo_base]
  exact DFunLike.congr_fun same B

end YM.Integration.WilsonIndependentSpoutThermalLog
