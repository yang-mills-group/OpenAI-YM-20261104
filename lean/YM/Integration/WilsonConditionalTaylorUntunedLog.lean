import YM.Integration.WilsonConditionalTaylorPulledWick
import YM.Integration.WilsonConditionalTaylorSceneCalibration
import YM.Integration.WilsonMovingExponentialConvention

/-! Read the historical *pre-reset* vacuum at every real field using the
original Gaussian, barycentre, Haar Jacobian and incoming interaction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorUntunedLog

open Matrix PowerSeries Lattice RG Push.Uniform Wilson Tree Exterior Precision
open PertExtension.Chart MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal MSbar.Midpoint
open FormalBulk08 FormalBulk08.Series WilsonMovingNormalizedBank
open WilsonConditionalTaylorWick WilsonConditionalTaylorSceneChoices WilsonConditionalTaylorSceneCalibration
open PhysicalNext.Repeat.Legato Comparison.RG02
open scoped Classical Matrix

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem vacuum (B : Matrix J I ℝ) (x : J→ℝ) (Q : Matrix I I ℝ)
    (pos : Q.PosDef) (f : PowerSeries (MvPolynomial J ℝ)) (zero : Kind f) :
    view x (confect (B*Q*B.transpose) f)=covelog (contract B x Q (Spring f)) := by
  let T:=confect (B*Q*B.transpose) f
  have clean : Kind T:=sugar _ zero
  have measured:=WilsonMovingNormalizedBank.vacuum B x pos f zero
  rw [WilsonMovingWickCoefficient.complete B x Q (Matrix.isHermitian_iff_isSymm.mp pos.isHermitian)
    pos.posSemidef,←WilsonMovingExponentialConvention.exp T clean,
    show view x (expan T)=expan (view x T) from map_expan _ clean] at measured
  have head : coeff 0 (view x T)=0:=by rw [view,coeff_map,show coeff 0 T=0 from clean,map_zero]
  exact (covelog_after head).symm.trans (congrArg covelog measured)

omit [Fintype I] [DecidableEq I] in
theorem centered (T : PowerSeries (Pot I)) (x z : I→ℝ) : view x (Rewind T z)=view x T-view z T := by
  ext1 i
  simp only [view,Rewind,coeff_map,coeff_mk,rewind,map_sub,MvPolynomial.eval_C]

variable {G : Gauge} {c f : Side} {S : StepData c f}

def filed (F : Forest S.ratio) (t : S.Choices) (X : PathData G) (p : Clip) (O : ChartRatio G)
    (T : Nesting G f) (h : fieldDir G c 1→AxisChart G F) (x : Positions (Primary c G)) : PowerSeries ℝ :=
  contract (straight F G) ((poring F h)*ᵥx) (Push.Uniform.block (priced F t p X) 0)⁻¹ (Spring (barbed F t O T))

theorem one (F : Forest S.ratio) (t : S.Choices) (X : PathData G) (p : Clip) (O : ChartRatio G)
    (T : Nesting G f) (h : fieldDir G c 1→AxisChart G F) (x : Positions (Primary c G))
    (bought : (Push.Uniform.block (priced F t p X) 0).PosDef) (clean : Kind T) :
    view x (colorCut F t X p O T h)=covelog (filed F t X p O T h x)-covelog (filed F t X p O T h 0) := by
  rw [colorCut,centered,song,WilsonConditionalTaylorPulledWick.pulled,WilsonConditionalTaylorPulledWick.pulled]
  exact congrArg₂ (·-·) (vacuum (straight F G) _ _ bought.inv _ (well F t O T clean))
    (vacuum (straight F G) _ _ bought.inv _ (well F t O T clean))

theorem actual (R : Run G) {N n k r : ℕ} {S : Scene R.family.path.levels n r} {u : G.ColorIndex}
    (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S) (j : ℕ) (lo : k≤j) (hi : j<N)
    (x : Positions (Primary (R.family.side j n) G)) :
    let F:=(scene.step j hi lo).choose
    let t:=issued R scene j lo hi
    let X:=R.alloy.B.kin.path N (j+1)
    let p:=(R.family.path.levels.params (j+1)).clip
    let h:=R.alloy.B.kin.stationary N j n F
    let bank:=filed F t X p R.metals.O (S.Poly (j+1)) h
    view x (untuned R scene j lo hi)=covelog (bank x)-covelog (bank 0) := by
  intro F t X p h bank
  let book:=RunFormalChain.fromRun R
  have seed:=(scene.budget (j+1) hi (lo.trans (Nat.le_succ j))).1
  apply one
  · exact blueprint F t X p (R.family.path.levels.blocks j n).branches seed.quiet
      (book.post.price _) (book.planned.gap N j n hi F)
  · exact seed.bond

end YM.Integration.WilsonConditionalTaylorUntunedLog
end

