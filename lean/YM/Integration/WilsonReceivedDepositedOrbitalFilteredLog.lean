import YM.Integration.WilsonReceivedDepositedOrbitalGrade
import YM.Integration.WilsonReceivedDepositedOrbitalKinetic

/-! A common retained thermal degree suffices for the true normalized marked log on one occupied subset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalFilteredLog
open Finset Function PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators
variable {I U V:Type}[DecidableEq I]

private theorem equivalence {S:Type}[CommRing S](k:ℕ)(f g:PowerSeries S):
    Ideal.Quotient.mk (Ideal.span ({(X:PowerSeries S)^k}:Set _)) f=
      Ideal.Quotient.mk (Ideal.span ({(X:PowerSeries S)^k}:Set _)) g ↔ Equal k f g:=by
  rw [Ideal.Quotient.eq,Ideal.mem_span_singleton,equal_iff]

theorem through (k:ℕ){M M' L L':Finset I→Ink U}(law:Equation M L)(law':Equation M' L')
    (s:Finset I)(admitted:∀t⊆s,Equal k (M t) (M' t)):Equal k (L s) (L' s):=by
  let f:=Ideal.Quotient.mk (Ideal.span ({(X:Ink U)^k}:Set _))
  let names:s↪I:=Embedding.subtype (·∈s)
  have contained (r:Finset s):r.map names⊆s:=by
    intro a ha
    obtain ⟨u,_,rfl⟩:=mem_map.mp ha
    exact u.property
  have left:Equation (fun r:Finset s=>f (M (r.map names))) (fun r:Finset s=>f (L (r.map names))):=
    (WilsonReceivedDepositedOrbitalGrade.restrict names law).mapKin f
  have right:Equation (fun r:Finset s=>f (M' (r.map names))) (fun r:Finset s=>f (L' (r.map names))):=
    (WilsonReceivedDepositedOrbitalGrade.restrict names law').mapKin f
  have masks:(fun r:Finset s=>f (M (r.map names)))=(fun r:Finset s=>f (M' (r.map names))):=by
    funext r
    exact (equivalence k _ _).2 (admitted _ (contained r))
  rw [masks] at left
  let scalar:ℝ→+*(Ink U ⧸ Ideal.span ({(X:Ink U)^k}:Set _)):=f.comp (PowerSeries.C.comp MvPolynomial.C)
  haveI:IsAddTorsionFree (Ink U ⧸ Ideal.span ({(X:Ink U)^k}:Set _)):=by
    constructor
    intro n hn x y h
    have invertible:IsUnit (scalar (n:ℝ)):=(isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)).map scalar
    rw [map_natCast] at invertible
    exact invertible.mul_left_cancel (by simpa only [nsmul_eq_mul] using h)
  have terminated:=congrFun (Equation.unique _ _ _ left right) s.attach
  change f (L (s.attach.map (Embedding.subtype (·∈s))))=f (L' (s.attach.map (Embedding.subtype (·∈s)))) at terminated
  rw [Finset.attach_map_val] at terminated
  exact (equivalence k _ _).1 terminated

theorem canceled (k:ℕ){a P Q:Ink U}(unit:constantCoeff a=1)(seen:Equal k (a*P) (a*Q)):
    Equal k P Q:=by
  let f:=Ideal.Quotient.mk (Ideal.span ({(X:Ink U)^k}:Set _))
  have one:IsUnit a:=PowerSeries.isUnit_iff_constantCoeff.mpr (unit ▸ isUnit_one)
  have paid:f a*f P=f a*f Q:=by simpa only [map_mul] using (equivalence k _ _).2 seen
  exact (equivalence k _ _).1 ((one.map f).mul_left_cancel paid)

theorem wick [Fintype U][Fintype V](G:Matrix U U ℝ)(k:ℕ){P Q:Ink (U⊕V)}(entry:Equal k P Q):
    Equal k (Wick V G P) (Wick V G Q):=by
  have heat:=overlayEq entry (glaze (fillSlots V G))
  intro a ha
  change coeff a (PowerSeries.map _ (fullB V G P))=coeff a (PowerSeries.map _ (fullB V G Q))
  simp only [PowerSeries.coeff_map,heat a ha]

theorem kinetic (c:Cost)(k:ℕ){P Q:Ink U}(entry:Equal k P Q):Equal k (redo c P) (redo c Q):=by
  apply filtered _ entry
  rw [redo_X,map_mul,constantCoeff_X,mul_zero]

end YM.Integration.WilsonReceivedDepositedOrbitalFilteredLog
end
