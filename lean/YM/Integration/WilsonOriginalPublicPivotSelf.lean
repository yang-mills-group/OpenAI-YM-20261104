import YM.Integration.WilsonOriginalPublicPivotCross

/-! Coercivity of the authenticated full reflected coordinate at finite
physical input, tested against its actual finite compensated primitive. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.Integration.WilsonOriginalPublicPivotSelf
open Filter Finset Function Lattice RG Wilson Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open Source MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicWickGram (nodes reading)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicPivotCross (Film detector left right old)
open scoped Classical BigOperators
variable {G:Gauge} {B:Local.Physical.Deck G} {h:ℕ} {I:Type} [Fintype I]
    (R:Run G) (W:Initialize G)
theorem original (axis:Axis)(leg:I→Glyph B h)(entire:Injective leg):
    ∃k τ:ℝ,0<k ∧ 0<τ ∧
    ∀ {L:Type} [Fintype L](d:Fin 2→ℕ)(v:(i:Fin 2)→(R.family.labels.level (d i)).Coeff)
      (X:L→Sample 2)(μ:L→ℂ)(q:ℕ)(g:ℝ)(coarse:ℂ)(a:I→ℂ)(A B:I→Film W)
      (c z u e t:ℝ),
      let H:=detector W X μ q g
      let U:=left R W d v a A
      let V:=right R W d v a B
      0≤c → 1≤z → 0≤u → e*u≤1 → e*u^2≤1 → t≤1 →
      ‖(fun i j=>H (A i*B j))-reading axis (nodes axis) leg‖≤τ →
      ‖coarse‖≤c*z^2 → ‖sampled R W d v X μ univ q g-coarse‖≤1 →
      (∑i,‖H (A i*V)‖)≤e*u → (∑i,‖H (U*B i)‖)≤e*u →
      ‖old R W d v X μ q g+H (U*V)‖≤e*u^2+t →
      ‖a‖≤ max 1 ((c+5)/k)*z:=by
  obtain ⟨k,τ,kp,tp,det⟩:=WilsonOriginalPublicPivotReflected.original R W axis leg entire
  refine ⟨k,τ,kp,tp,?_⟩
  intro L inst d v X μ q g coarse a A B c z u e t H U V cp zp up first both last near capped actual
    leftC rightC cross
  exact det d v X μ q g coarse (fun i j=>H (A i*B j)) a c z u e t cp zp up first both last
    near capped actual (WilsonOriginalPublicPivotCross.difference R W d v X μ q g a A B leftC rightC cross)

end YM.Integration.WilsonOriginalPublicPivotSelf
end
