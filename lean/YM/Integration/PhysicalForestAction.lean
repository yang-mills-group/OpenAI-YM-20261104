import YM.WilsonCoeffUV.Kinetic.Bridge
import YM.Comparison.RG02.Bulk.Fk
import YM.FVAAlt2.Boot.Start

/-! Transport of the original finite unmarked action through the nonlinear
forest chart, including the physical row at every coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalForestAction

open Function Filter Lattice Wilson RG Precision Exterior Tree
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Power.Roam FreeResolvent Comparison.RG02
open MeasureTheory Stationary Marker Multi Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
variable (M : Matrix (Woods G f) (Woods G c) ℝ)
variable (ρ : fieldDir G c 1 → AxisChart G F)
variable {p : Clip} {P : PathData G} {O : ChartRatio G}
variable {V : Type} [DecidableEq V] {C : Census V}

def physical (w : Sloc S F G) : Bulk.SliceDir S F G :=
  (badge S F w, (sedan S F ρ w).1)

def field (w : Sloc S F G) : Config G f := mantle (camSlice G S F M *ᵥ w)

def absoluteAction (W : Bulk.Colors C G f) (g : ℝ) (w : Sloc S F G) : ℝ :=
  mainTerm p P (field S F M w) + jointPen G S (panSlice G S F M *ᵥ w) +
  g^2 * (loop P (field S F M w) - unhaar O (camSlice G S F M *ᵥ w)) +
  W.vac g (field S F M w)

private theorem home (h : ρ 0 = 0) : physical S F ρ 0 = 0 := by
  apply Prod.ext
  · exact map_zero _
  · exact congrArg Prod.fst (sedan_zero S F ρ h)

private theorem smooth (h : ContDiffAt ℝ ω ρ 0) :
    ContDiffAt ℝ ω (physical S F ρ) 0 :=
  (badge_green S F).prodMk (contDiffAt_fst.comp 0 (sedan_green S F ρ h))

private theorem relativeHaar (h : ContDiffAt ℝ ω ρ 0) (h₀ : ρ 0 = 0)
    (hO : LocalRatio O) :
    ∀ᶠ w : Sloc S F G in 𝓝 0, Real.log (∏ i : F.Free, O.J ((physical S F ρ w).2 i)) =
      stampJ S F ρ O w := by
  have ht := (smooth S F ρ h).continuousAt.tendsto
  rw [home S F ρ h₀] at ht
  have hi (i : F.Free) : ∀ᶠ w : Sloc S F G in 𝓝 0,
      0 < O.J ((physical S F ρ w).2 i) := by
    have he := (((continuous_apply i).comp continuous_snd).tendsto (0 : Bulk.SliceDir S F G)).comp ht
    exact (he.eventually (Metric.ball_mem_nhds (0 : G.Color) hO.patch)).mono fun v hv => hO.pos _ hv
  filter_upwards [eventually_all.mpr hi] with w hw
  rw [Real.log_prod (fun i (_ : i ∈ Finset.univ) => (hw i).ne')]
  exact (prism S F (physical S F ρ w).2 O hO).symm

theorem action_germ (K : Bulk.Kernel S p P O) (t : S.Choices) (W : Bulk.Colors C G f)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M))
    (h : ContDiffAt ℝ ω ρ 0) (h₀ : ρ 0 = 0) :
    ∀ᶠ w : Sloc S F G in 𝓝 0, ∀ g : ℝ,
      Bulk.geometric K F t W (g,physical S F ρ w) =
      absoluteAction S F M (p:=p) (P:=P) (O:=O) W g (Cameo.spider (shore S F M ρ) w) -
        g^2 * Real.log (edgeM (shore S F M ρ) w).det := by
  have ht := (smooth S F ρ h).continuousAt.tendsto
  rw [home S F ρ h₀] at ht
  filter_upwards [tilted S F M ρ hM h h₀, shape_area S F M ρ O h h₀ K.ratio hM,
    ht.eventually (Work.F04.tested_germ K.branches F p P t (tac S)),
    relativeHaar S F ρ h h₀ K.ratio] with w hU hJ hθ hw
  let v := Cameo.spider (shore S F M ρ) w
  have hU' : field S F M v = Work.F03.live F (physical S F ρ w) := hU
  have harea : Real.log (edgeM (shore S F M ρ) w).det +
      unhaar O (camSlice G S F M *ᵥ v) = stampJ S F ρ O w := by
    have hp : 0 < (edgeM (shore S F M ρ) w).det *
        Real.exp (unhaar O (camSlice G S F M *ᵥ v)) := by
      rw [hJ]
      exact Real.exp_pos _
    have hd : 0 < (edgeM (shore S F M ρ) w).det :=
      (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp hp
    have hl := congrArg Real.log hJ
    rwa [Real.log_mul hd.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp] at hl
  have hcost : Bulk.Surface S p P F t (physical S F ρ w) =
      mainTerm p P (field S F M v) + jointPen G S (panSlice G S F M *ᵥ v) := by
    change uncurry (tested F t p P) (physical S F ρ w) = _
    rw [hθ, jointPen, arm_pan]
    change mainTerm p P (Work.F03.live F (physical S F ρ w)) +
      noiseTaylor S (represent (badge S F w)) (Work.F03.live F (physical S F ρ w)) (tac S) =
      mainTerm p P (field S F M v) + noiseTaylor S (mantle (rightArm w)) (field S F M v) (tac S)
    rw [hU']
    rfl
  intro g
  change Bulk.Surface S p P F t (physical S F ρ w) +
    (g^2 * (loop P (Work.F03.live F (physical S F ρ w)) -
      Real.log (∏ i : F.Free, O.J ((physical S F ρ w).2 i))) +
      W.vac g (Work.F03.live F (physical S F ρ w))) = _
  rw [hcost, hw, ← hU', ← harea]
  unfold absoluteAction
  change _ = mainTerm p P (field S F M v) + jointPen G S (panSlice G S F M *ᵥ v) +
    g^2 * (loop P (field S F M v) - unhaar O (camSlice G S F M *ᵥ v)) +
    W.vac g (field S F M v) - g^2 * Real.log (edgeM (shore S F M ρ) w).det
  ring

theorem linear_action (K : Bulk.Kernel S p P O) (t : S.Choices) (W : Bulk.Colors C G f)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M)) :
    let D := fderiv ℝ (K.b F) 0
    ∀ᶠ w : Sloc S F G in 𝓝 0, ∀ g : ℝ,
      Bulk.geometric K F t W (g,physical S F D w) =
      absoluteAction S F M (p:=p) (P:=P) (O:=O) W g (Cameo.spider (shore S F M D) w) -
        g^2 * Real.log (edgeM (shore S F M D) w).det := by
  intro D
  exact action_germ S F M D K t W hM D.contDiff.contDiffAt (map_zero D)

section opening
open RegulatorIR.FVAAlt2
variable (Γ : History G) (L : Bulk.Chain Γ) (N n : ℕ) {m : ℕ}
variable (u : V) (T : Boot.Scout (G:=G) m)
variable {c₀ : Side} (S₀ : StepData c₀ (Γ.S.side N n)) (F₀ : Forest S₀.ratio)
variable (M₀ : Matrix (Woods G (Γ.S.side N n)) (Woods G c₀) ℝ)

include L in
theorem opening (g : ℝ) (w : Sloc S₀ F₀ G) :
    absoluteAction S₀ F₀ M₀ (p:=(Γ.rep N n N).clip) (P:=(Γ.rep N n N).path) (O:=O)
      (Boot.ink C u Γ N n T) g w =
      eWilson (camSlice G S₀ F₀ M₀ *ᵥ w) + jointPen G S₀ (panSlice G S₀ F₀ M₀ *ᵥ w) -
      g^2 * unhaar O (camSlice G S₀ F₀ M₀ *ᵥ w) := by
  unfold absoluteAction
  rw [Boot.kept0 Γ L N n]
  change mainTerm (Γ.rep N n N).clip (Γ.rep N n N).path _ + _ + g^2 * (0 - _) +
    (Wilson.energy (field S₀ F₀ M₀ w) - mainTerm (Γ.rep N n N).clip (Γ.rep N n N).path _) =
    Wilson.energy (field S₀ F₀ M₀ w) + _ - _
  ring

end opening
end YM.Integration.PhysicalForestAction
