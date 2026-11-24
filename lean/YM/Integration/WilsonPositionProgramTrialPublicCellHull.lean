import YM.Integration.WilsonPositionProgramTrialPublicCellRoom
import YM.Integration.WilsonIndependentMatchedOpeningExtent

/-! A finite menu for every registered test jet over all fractional offsets in the physical cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellHull
open Function Filter Set Lattice WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider
open WilsonIndependentFittedExteriorProfile (home)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open scoped Classical BigOperators
variable {D:ℕ}

def hull (T:Rarity D)(x y σ:ℝ)(o:CellR):Finset Cover:=
  let R:=max 1 (|y| *‖o.val‖+x+T.radius*σ)
  let B:=(R+|y|+x)/x
  Fintype.piFinset (fun _:Axis=>Finset.Icc ⌈-B⌉ ⌊B⌋)

theorem original (T:Rarity D){x:ℝ}(xp:0<x)(y σ:ℝ)(sp:0<σ)(o:CellR)
    (ξ:Point4)(bounded:‖ξ‖≤1):VisitsT (placed T x y σ sp o ξ) x y o⊆hull T x y σ o:=by
  let F:=placed T x y σ sp o ξ
  let R:=max 1 (|y| *‖o.val‖+x+T.radius*σ)
  let B:=(R+|y|+x)/x
  have radius:F.radius≤R:=by
    change max 1 (‖-(y•o.val)-x•ξ‖+T.radius*σ)≤ max 1 _
    apply max_le_max_left
    have ht:=norm_sub_le (-(y•o.val)) (x•ξ)
    rw [norm_neg,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_of_nonneg xp.le] at ht
    linarith only [ht,mul_le_mul_of_nonneg_left bounded xp.le]
  intro z seat
  have live:wheelC x y z F.ψ o≠0:=(visiting xp).mp seat
  have extent:‖actualW z‖≤B:=by
    apply (le_div_iff₀ xp).2
    have fee:=hall_fit F x y o z live
    rw [abs_of_pos xp] at fee
    linarith only [fee,radius]
  apply Fintype.mem_piFinset.mpr
  intro e
  have slot:|(z e:ℝ)|≤B:=by
    change ‖actualW z e‖≤B
    exact (norm_le_pi_norm (actualW z) e).trans extent
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (abs_le.mp slot).1,Int.le_floor.mpr (abs_le.mp slot).2⟩

theorem inactive (T:Rarity D){x:ℝ}(xp:0<x)(y σ:ℝ)(sp:0<σ)(o:CellR)
    (ξ:Point4)(bounded:‖ξ‖≤1){z:Cover}(outside:z∉hull T x y σ o):
    wheelC x y z (placed T x y σ sp o ξ).ψ o=0:=by
  by_contra active
  exact outside (original T xp y σ sp o ξ bounded ((visiting xp).mpr active))

end YM.Integration.WilsonPositionProgramTrialPublicCellHull
end
