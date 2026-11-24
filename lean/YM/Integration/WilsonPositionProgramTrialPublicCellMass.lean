import YM.Integration.WilsonViewerAffineCells
import YM.Integration.WilsonMeasuredPublicEntranceCoverCells

/-! Disintegrate each covered physical cell on one fractional domain,
retaining the original ceiling convention and the entire joint Jacobian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellMass
open Function Filter Finset Set MeasureTheory Lattice Extraction RG
open Wilson Source Extra.Histories Spec PhysicalNext.Repeat.Legato
open WilsonViewerAffineCells (pull anchor)
open WilsonMeasuredPublicEntranceCoverCells (cube mass)
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}

theorem digits (R:Run G){r:ℝ}(rp:0<r)(K:ℕ)(z:Fin n → Cover)(ξ:Points n):
    address (R.family.S.a K) (r • pull (R:=R) r K z ξ)=address 1 ξ+z:=by
  funext i a
  change ⌈(r*(r⁻¹*(R.family.S.a K*(z i a:ℝ))+(R.family.S.a K/r)*ξ i a))/R.family.S.a K⌉=
    ⌈ξ i a/1⌉+z i a
  have coord:(r*(r⁻¹*(R.family.S.a K*(z i a:ℝ))+(R.family.S.a K/r)*ξ i a))/R.family.S.a K=
      ξ i a+(z i a:ℝ):=by field_simp [rp.ne',(R.family.S.a_pos K).ne'];ring
  rw [coord,div_one,Int.ceil_add_intCast]

theorem cell (R:Run G){r:ℝ}(rp:0<r)(K:ℕ)(z:Fin n → Cover)(ξ:Points n):
    pull (R:=R) r K z ξ∈cube (R.family.S.a K) r z ↔ ξ∈cube 1 1 0:=by
  change address (R.family.S.a K) (r • pull (R:=R) r K z ξ)=z ↔ address 1 ((1:ℝ) • ξ)=0
  rw [digits R rp,one_smul]
  simp

theorem original (R:Run G){r:ℝ}(rp:0<r)(K:ℕ)(z:Fin n → Cover)(Φ:Test n):
    mass Φ (R.family.S.a K) r z=(R.family.S.a K/r)^(4*n) •
      ∫ξ in cube 1 1 (0:Fin n → Cover),Φ (pull (R:=R) r K z ξ):=by
  let V:=cube (R.family.S.a K) r z
  let U:=cube 1 1 (0:Fin n → Cover)
  let Y:=V.indicator fun x:Points n=>Φ x
  let b:=anchor (R:=R) r K z
  let h:=R.family.S.a K/r
  have hp:0<h:=div_pos (R.family.S.a_pos K) rp
  have measureV:MeasurableSet V:=WilsonMeasuredPublicEntranceCoverCells.visible _ _ (R.family.S.a_pos K) _
  have measureU:MeasurableSet U:=WilsonMeasuredPublicEntranceCoverCells.visible _ _ one_pos _
  have changeCell (ξ:Points n):Y (b+h • ξ)=U.indicator (fun t=>Φ (pull (R:=R) r K z t)) ξ:=by
    by_cases hx:ξ∈U
    · have hz:b+h • ξ∈V:=(cell R rp K z ξ).mpr hx
      rw [show Y (b+h • ξ)=Φ (b+h • ξ) from Set.indicator_of_mem hz _,Set.indicator_of_mem hx]
      rfl
    · have hz:b+h • ξ∉V:=fun hit=>hx ((cell R rp K z ξ).mp hit)
      rw [show Y (b+h • ξ)=0 from Set.indicator_of_notMem hz _,Set.indicator_of_notMem hx]
  have scale:=Measure.integral_comp_smul_of_nonneg volume (fun x:Points n=>Y (b+x)) h (hR:=hp.le)
  rw [Next.UVStress.point_dimension,integral_add_left_eq_self] at scale
  calc
    mass Φ (R.family.S.a K) r z=∫x:Points n,Y x:=(integral_indicator (f:=fun x=>Φ x) (μ:=volume) measureV).symm
    _=h^(4*n) • ∫ξ:Points n,Y (b+h • ξ):=by
      rw [scale,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hp.ne'),one_smul]
    _=_:=by simp_rw [changeCell];rw [integral_indicator measureU]

end YM.Integration.WilsonPositionProgramTrialPublicCellMass
end
