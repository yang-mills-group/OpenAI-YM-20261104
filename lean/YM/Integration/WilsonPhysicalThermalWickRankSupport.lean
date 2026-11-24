import YM.Integration.WilsonPhysicalThermalWickLabels
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Basis

/-! Preserve every nonzero coordinate of a counted field, including a
free-equation coordinate, until its actual thermal input is fitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickRankSupport
open Lattice RG Wilson Labels MvPolynomial
open Next.Rank Next.Rank.Configuration
open WilsonPhysicalThermalWickRescale (pure)
open scoped BigOperators Classical
variable {G:Gauge}{d h:ℕ}

def Counted (F:Frame G d)(y:F.Coeff)(q:ℕ):Prop:=
  ∀t:ℝ,F.scaled t y=((t^q:ℝ):ℂ)•y

theorem axis (F:Frame G d)(i:F.Index):Counted F (Pi.single i 1) (F.grades i).2:=by
  intro t
  simpa only [F.coords_basis] using F.scaled_pure t (F.grades i) (F.pure i)

theorem support (F:Frame G d)(y:F.Coeff)(q:ℕ)(h:Counted F y q)(i:F.Index)
    (kept:y i≠0):(F.grades i).2=q:=by
  have e:=congrFun (h 2) i
  simp only [Frame.scaled_apply,Pi.smul_apply,smul_eq_mul] at e
  have eq:(2:ℝ)^(F.grades i).2=(2:ℝ)^q:=Complex.ofReal_injective (mul_right_cancel₀ kept e)
  exact (pow_right_injective₀ (show (0:ℝ)<2 by norm_num) (show (2:ℝ)≠1 by norm_num)) eq

theorem polynomial (F:Frame G d)(y:F.Coeff)(q:ℕ)(count:Counted F y q)(raise:d≤h):
    pure q (thawKey (raiseLabel G raise (F.coords.symm y))):=by
  have reprint:thawKey (raiseLabel G raise (F.coords.symm y))=
      ∑i,y i•thawKey (raiseLabel G raise (F.basis i)):=by
    apply (rename_injective (R:=ℂ) (f:=(Subtype.val :KeyIn G h→Key G)) Subtype.val_injective)
    simp only [returns,map_sum,map_smul]
    change (F.coords.symm y).val=∑i,y i•(F.basis i).val
    have fromBasis:=congrArg (fun x:Label G d=>x.val) (F.basis.sum_repr (F.coords.symm y))
    simpa only [AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul_of_tower,
        show ∀i,F.basis.repr (F.coords.symm y) i=y i from fun i=>congrFun (F.coords.apply_symm_apply y) i] using
      fromBasis.symm
  intro m hm
  by_contra bad
  have z:coeff m (thawKey (raiseLabel G raise (F.coords.symm y)))=0:=by
    rw [reprint,coeff_sum]
    refine Finset.sum_eq_zero fun i _=>?_
    rw [coeff_smul]
    by_cases hy:y i=0
    · rw [hy,zero_smul]
    · have off:m∉(thawKey (raiseLabel G raise (F.basis i))).support:=fun hi=>
        bad ((WilsonPhysicalThermalWickLabels.axis F i raise m hi).trans (support F y q count i hy))
      rw [notMem_support_iff.mp off,smul_zero]
  exact (mem_support_iff.mp hm) z

end YM.Integration.WilsonPhysicalThermalWickRankSupport
end
