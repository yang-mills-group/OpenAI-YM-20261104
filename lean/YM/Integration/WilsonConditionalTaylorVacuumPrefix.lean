import YM.Integration.WilsonConditionalTaylorUntunedLog
import YM.Integration.WilsonMovingVacuumConstant

/-! Finite-order stability of the true field-dependent vacuum under
changes of the unpaid tail and the spatially constant free energy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorVacuumPrefix
open Matrix PowerSeries Lattice RG Push.Uniform Wilson Tree Exterior Precision
open PertExtension.Chart MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal MSbar.Midpoint
open FormalBulk08 Series WilsonConditionalTaylorWick WilsonConditionalTaylorUntunedLog
open WilsonMovingVacuumConstant WilsonMovingNormalizedBank
open scoped Classical Matrix
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem initial (B : Matrix J I ℝ) (x : J→ℝ) (Q : Matrix I I ℝ) (pos : Q.PosDef)
    (f : PowerSeries (MvPolynomial J ℝ)) (hf : Kind f) : coeff 0 (contract B x Q (Spring f))=1:=by
  change coeff 0 (beam _ _)=1
  rw [←WilsonMovingWickCoefficient.complete B x Q (Matrix.isHermitian_iff_isSymm.mp pos.isHermitian)
    pos.posSemidef (Spring f)]
  exact WilsonMovingGaussianResponse.first Q B x (Spring f) (covers hf)

theorem logarithm {s v : PowerSeries ℝ} (low : coeff 0 s=0) (base : coeff 0 v=1) :
    covelog (expan s*v)=s+covelog v:=by
  have z : coeff 0 (s+covelog v)=0:=by rw [map_add,low,covelog_rank base,zero_add]
  calc
    _=covelog (expan (s+covelog v)):=by rw [←expan_mul low (covelog_rank base),expan_after base]
    _=_:=covelog_after z

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (F : Forest S.ratio) (t : S.Choices) (X : PathData G) (p : Clip) (O : ChartRatio G)
variable (h : fieldDir G c 1→AxisChart G F) (bought : (Push.Uniform.block (priced F t p X) 0).PosDef)

include bought in
theorem tail {A B : Nesting G f} {m : ℕ} (hA : Kind A) (hB : Kind B) (cut : Through m A B)
    (x : Positions (Primary c G)) :
    Through m (view x (colorCut F t X p O A h)) (view x (colorCut F t X p O B h)):=by
  rw [one F t X p O A h x bought hA,one F t X p O B h x bought hB]
  have before : Through m (barbed F t O A) (barbed F t O B) :=
    (Through.exact_eq _ _).add (cut.map_left (rail (taps F G)).toRingHom)
  have exp := before.expan_congr (well F t O A hA)
  rw [WilsonMovingExponentialConvention.exp _ (well F t O A hA),
    WilsonMovingExponentialConvention.exp _ (well F t O B hB)] at exp
  have atPoint (v : Positions (Primary c G)) : Through m (covelog (filed F t X p O A h v)) (covelog (filed F t X p O B h v)):=by
    apply Through.cove_congr
    · exact beam_through _ (exp.map_left _)
    · exact initial _ _ _ bought.inv _ (well F t O A hA)
  exact (atPoint x).sub (atPoint 0)

private theorem affine {I J : Type} [Fintype I] [Fintype J] (L : Matrix I J ℝ) (s : PowerSeries ℝ) :
    PowerSeries.map (rail L).toRingHom (WilsonMovingVacuumConstant.scalar I s)=WilsonMovingVacuumConstant.scalar J s:=by
  ext1 e
  simp only [WilsonMovingVacuumConstant.scalar,coeff_map]
  exact (rail L).commutes _

include bought in
theorem constant (A : Nesting G f) (hA : Kind A) (s : PowerSeries ℝ) (hs : coeff 0 s=0)
    (x : Positions (Primary c G)) :
    view x (colorCut F t X p O (A+WilsonMovingVacuumConstant.scalar (Primary f G) s) h)=view x (colorCut F t X p O A h):=by
  have hC : Kind (A+WilsonMovingVacuumConstant.scalar (Primary f G) s):=by
    change coeff 0 (A+WilsonMovingVacuumConstant.scalar (Primary f G) s)=0
    rw [map_add,hA,WilsonMovingVacuumConstant.scalar,coeff_map,hs,map_zero,add_zero]
  have active : barbed F t O (A+WilsonMovingVacuumConstant.scalar (Primary f G) s)=barbed F t O A+WilsonMovingVacuumConstant.scalar (Joint F G) s:=by
    unfold barbed
    rw [map_add,affine,add_assoc]
  have bank (v : Positions (Primary c G)) : filed F t X p O (A+WilsonMovingVacuumConstant.scalar (Primary f G) s) h v =
      expan s * filed F t X p O A h v:=by
    unfold filed
    rw [active,action _ (well F t O A hA) s hs,paid]
  have first (v : Positions (Primary c G)) : coeff 0 (filed F t X p O A h v)=1 :=
    initial _ _ _ bought.inv _ (well F t O A hA)
  rw [one F t X p O _ h x bought hC,one F t X p O A h x bought hA,bank,bank,
    logarithm hs (first x),logarithm hs (first 0)]
  ring

include bought in
theorem received {m : ℕ} {A B : Nesting G f} (hA : Kind A) (hB : Kind B)
    (s : PowerSeries ℝ) (hs : coeff 0 s=0) (pre : Through m A (B+WilsonMovingVacuumConstant.scalar (Primary f G) s)) :
    Through m (colorCut F t X p O A h) (colorCut F t X p O B h):=by
  have hC : Kind (B+WilsonMovingVacuumConstant.scalar (Primary f G) s):=by
    change coeff 0 (B+WilsonMovingVacuumConstant.scalar (Primary f G) s)=0
    rw [map_add,hB,WilsonMovingVacuumConstant.scalar,coeff_map,hs,map_zero,add_zero]
  intro e he
  apply Jets.orbit_ext
  intro x
  have same:=tail F t X p O h bought hA hC pre x e he
  rw [constant F t X p O h bought B hB s hs x] at same
  exact same

end YM.Integration.WilsonConditionalTaylorVacuumPrefix

