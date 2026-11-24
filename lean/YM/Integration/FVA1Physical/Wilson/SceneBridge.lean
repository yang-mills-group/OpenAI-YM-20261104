import YM.Integration.FVA1Physical.Wilson.MeasuredCanon
import YM.MSbar.Lis.Aspire
import YM.MSbar.Ballet.Visor

/-! Realized vacuum scenes and the independent local Wilson step, in the
same coarse-field coordinates. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato Comparison.RG02
open MSbar MSbar.Rolling MSbar.Wave MSbar.Midpoint Push Push.Uniform Precision
open scoped Classical

variable {G : Gauge} {c f : Side} (T : StepData c f)

/-- The auxiliary kernel normalization cancels at the origin, retaining
the exact, interacting Haar integral in the denominator. -/
theorem shunt_is_physical (F : ℝ → Config G f → ℝ) (g : ℝ) (U : Config G c) :
    shunt T F g U =
      T.push (Integral.temperature g) (F g) U / T.push (Integral.temperature g) (F g) 1 := by
  unfold shunt boxS
  rw [earnsH,earnsH]
  simp only [Integral.temperature, inv_pow]
  exact mul_div_mul_left _ _ (nut_pos G T _).ne'

variable (A : Run G) {N p k r j : ℕ} {e : G.Color}
    {S : Scene A.family.path.levels p r}

/-- At every retained scale, including an inherited one, the actual density
in the scene is exactly a normalized physical block step applied to the full
preceding scene. Both numerator and denominator use the same retuned coupling. -/
theorem scene_step_density (hS : Realized (RunFormalChain.fromRun A).kin N p k r e S)
    (hj : j < N) (hk : k ≤ j) (g : ℝ) (U : Config G (A.family.side j p)) :
    let t := tiltMap (S.action j) r g
    let T := A.family.path.levels.clock.op j p
    S.film j g U = T.push (Integral.temperature t) (S.film (j+1) t) U /
      T.push (Integral.temperature t) (S.film (j+1) t) 1 := by
  obtain ⟨_,_,_,eqn,_⟩ := hS.step j hj hk
  rw [eqn]
  exact shunt_is_physical _ _ _ _

/-- Before retuning, at the first inherited level and the measured initial
coupling, the scene's push is literally the retained physical density divided
by its value at the identity, at every background field. -/
theorem top_step_denominator (hS : Realized (RunFormalChain.fromRun A).kin (j+1) p k r e S)
    (U : Config G (A.family.side j p)) :
    let g := Pert.Asymptotics.regulatorRun A.family (j+1) p (j+1)
    let Q := A.family.path.rep (j+1) p j
    shunt (A.family.path.levels.clock.op j p) (S.film (j+1)) g U = Q.eval U / Q.eval 1 := by
  dsimp only
  rw [shunt_is_physical, hS.top0, Rolling.breed]
  let g := Pert.Asymptotics.regulatorRun A.family (j+1) p (j+1)
  have ht := Local.RealStep.trajectory A.family (j+1) p (j+1) A.makes le_rfl
  have ht' : g⁻¹ ^ 2 = Integral.temperature g := inv_pow g 2
  let β := (A.family.path.rep (j+1) p (j+1)).beta
  let T := A.family.path.levels.clock.op j p
  have step : (A.family.path.rep (j+1) p j).eval =
      T.push β (A.family.path.rep (j+1) p (j+1)).eval :=
    (A.makes.wilson.steps (j+1) p j (Nat.lt_succ_self _)).1
  have start : (A.family.path.rep (j+1) p (j+1)).eval = bare β :=
    (A.makes.wilson.starts (j+1) p).2
  rw [ht',ht,step,start]

/-- The full leading coarse-field polynomial in the normalized scene equals
the independent local Wilson vacuum action after any reset, at any inherited
depth, for every field, choice of forest and incoming colors. -/
theorem scene_zero_is_wilson {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    (D : LocalFormal.Datum A.family R)
    {S : Scene A.family.path.levels D.period r}
    (hS : Realized (RunFormalChain.fromRun A).kin D.cutoff D.period k r e S)
    (hk : k ≤ D.level) (cal : Adjacent.Caliber)
    (x : Positions (Primary (A.family.side D.level D.period) G)) :
    D.resetVacuumAction (RunFormalChain.fromRun A) cal r 0 (tint G _ x) =
      (Lis.atlas (S.Poly D.level) r 0 ((RunFormalChain.fromRun A).kin.path D.cutoff D.level)
        (A.family.path.levels.params D.level).clip x : ℂ) := by
  let L := RunFormalChain.fromRun A
  have ht := (hS.budget D.level D.below.le hk).1
  rw [D.resetVacuumAction_actual_quadratic, L.selected _ _ _ D.below.le,
    L.clips _ _ _ D.below.le]
  unfold Lis.atlas Wave.joy Wave.tariff
  rw [map_sub,PowerSeries.coeff_zero_C,ht.bond,zero_sub,map_neg,
    inkUnder r _ _ _ ht x,Complex.ofReal_neg]
  rfl

end YM.Integration.FVA1Physical.Wilson
