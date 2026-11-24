import YM.Integration.FVA1Physical.Wilson.ForestRecenter
import YM.Integration.FVA1Physical.Wilson.HotelChord

/-! The whole physical reading of a forest motion against an independent Wilson energy increment, including every failed exterior, on numerically certified cells. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}

def ForestCell.width (W : ForestCell Q R out) : ℝ :=
  W.J.C*shade G*(‖W.center‖+W.b+‖W.x‖)

/-- Numeric admissibility for a copied field in the independent Wilson chart.
All three tests compare scalar radii, uniformly in placements and periods. -/
def ForestCell.Fits (W : ForestCell Q R out) (g w : ℝ) : Prop :=
  W.width ≤ W.J.δ ∧ W.J.C*W.width<(LocalH.geom_patch G).choose ∧ W.J.C*W.width ≤ g*w

theorem ForestCell.wilson_on_test (W : ForestCell Q R out) (B : Positions (Primary f G)→ℝ)
    {g w : ℝ} (hg : 0 < g) (hw : 0 ≤ w) (fit : W.Fits g w)
    (t : IV W.F (board W.F W.X) G) (φ : Config G f→ℝ) :
    let O := represent (tint G (Exterior.Body 1 c) W.x)
    let area := hotel W.F W.X W.Y W.J O W.center W.a W.b
    let copy := chambers W.F W.Y W.J O W.center
    let κ := twirl W.F (board W.F W.X) t
    let r := woolModel W.F W.X W.J R W.Y W.source O W.center W.a W.b
    let q := Rota.ghat r t φ area
    (fun U=> q U*(R.eval (κ U)*Real.exp (moveBank R copy κ B g w (motionCost G W.X w) U))) =
    fun U=> q U*(R.eval (κ U)*Real.exp (B (chartLog g (copy U))-B (chartLog g (copy (κ U))))) := by
  intro O area copy κ r q
  funext U
  by_cases live : q U=0
  · rw [live,zero_mul,zero_mul]
  have orig : U∈area := by
    by_contra absent; apply live
    change spec area U*(r (κ U)*φ (κ U))=0
    rw [show spec area U=0 from Set.indicator_of_notMem absent _,zero_mul]
  have rotated : κ U∈area := by
    by_contra absent; apply live
    change spec area U*((spec area (κ U)*Real.exp _ / _)*φ (κ U))=0
    rw [show spec area (κ U)=0 from Set.indicator_of_notMem absent _,zero_mul,zero_div,zero_mul,mul_zero]
  have reg (D : Config G f) (h : D∈area) : copy D∈regularInputs g w :=
    chord_to_regular W.voice hg hw fit.1 fit.2.1 fit.2.2 (copy D)
      (fun e=> hotel_chord W.voice W.posture h e)
  have geom := (Posture.planT W.voice W.posture t orig rotated).2.old
  have ru := reg U orig
  have rv := reg (κ U) rotated
  have admissible : U∈moveEvent copy κ g w (motionCost G W.X w) :=
    ⟨⟨ru,rv⟩,spine_coordinates geom g w ru.2 rv.2⟩
  rw [moveBank,Set.piecewise_eq_of_mem _ _ _ admissible]

def ForestCell.PureReadout (W : ForestCell Q R out) (B : Positions (Primary f G)→ℝ)
    (g w ε fee C σ δ Λ forced ψ : ℝ) : Prop :=
  let O := represent (tint G (Exterior.Body 1 c) W.x)
  let I := board W.F W.X
  let A := hotel W.F W.X W.Y W.J O W.center W.a W.b
  let X := youth W.F W.Y
  let r := woolModel W.F W.X W.J R W.Y W.source O W.center W.a W.b
  let ζ := Real.exp (Posture.wSize G R.p σ C δ Λ R.beta W.M W.Y.card W.X.card W.P W.bound W.b)/
    Posture.moss G W.radius I.card
  let copy := chambers W.F W.Y W.J O W.center
  ∀ (t : IV W.F I G) (φ : Config G f→ℝ), GaugeLocal Q X φ → 0 ≤ φ → ∀ b, (∀ U, φ U ≤ b) →
    let κ := twirl W.F I t
    let q := Rota.ghat r t φ A
    let Z := Q.push R.beta R.eval O
    let charge := ψ*(R.p.mass X (ζ*b*2)*Real.exp (X.card*forced))
    |(Q.push R.beta (fun U=> q U*(R.eval (κ U)*Real.exp (B (chartLog g (copy U))-B (chartLog g (copy (κ U))))) ) O -
        Q.push R.beta (fun U=> q U*R.eval U) O)/Z| ≤ charge+2*(motionCost G W.X w*(ε/w)+fee)*(ζ*b+charge)

theorem ForestCell.pure_of_compares (W : ForestCell Q R out) (B : Positions (Primary f G)→ℝ)
    {g w ε fee C σ δ Λ forced ψ : ℝ} (hg : 0 < g) (hw : 0 ≤ w) (fit : W.Fits g w)
    (priced : W.Compares B g w ε (motionCost G W.X w) fee C σ δ Λ forced ψ) :
    W.PureReadout B g w ε fee C σ δ Λ forced ψ := by
  intro t φ localφ hφ b φB
  have paid := priced t φ localφ hφ b φB
  have changeWeight := W.wilson_on_test B hg hw fit t φ
  dsimp only at changeWeight paid ⊢
  rw [←changeWeight]
  exact paid

variable {C : Family G} (L : Bulk.Chain C.path)

theorem inherited_pure_readout (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (hp : p+3 ≤ m)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k:ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj:j < N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj).Room G)
        (t : (traversal T hj).Tags),
        let R := C.path.rep N n (j+1)
        let out := C.path.rep N n j
        let S' := C.path.levels.clock.op j n
        let cal := C.path.levels.clock
        let g := Heath.Stock.cue R.beta
        let w := Mosaic.vol (cal.hatBeta (j+1))
        let pred := C.path.levels.params (j+1)
        let B := boundaryBank L S T hj h t p g
        let ε := g^((p:ℝ)+1-η)
        ∀ (W : ForestCell S' R out) (ψ : ℝ), 0 ≤ ψ →
          Stock.Season W.J (C.path.levels.params j) pred (cal.hatBeta j) R out S' ψ →
          W.Fits g w → ∀ fee, 0 ≤ fee →
          silkRoad pred.paths pred.width (cal.allowance (j+1)) (cal.loopCap (j+1)) R.beta W.X.card W.M R.p W.d ≤ fee →
          motionCost G W.X w*(ε/w)+fee ≤ 1 → W.PureReadout B g w ε fee pred.paths pred.width
            (cal.allowance (j+1)) (cal.loopCap (j+1)) (cal.forcedAllowance (j+1)) ψ := by
  have high := Multi.Wage.hat_tend simple C.path.levels
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp ((Alto.broad.comp high).eventually_gt_atTop 0)
  filter_upwards [inherited_forest_readout L u simple sel D s p m hs hm hp hη,eventually_ge_atTop k₀] with k bought cutoff
  intro N n lo
  obtain ⟨S,hS,rows⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hk hj T h t R out S' cal g w pred B ε W ψ hψ season fit fee hfee price small
  have jk := hk.trans (Nat.le_succ j)
  have hw : 0 < w := div_pos (h₀ _ (cutoff.trans jk)) (by norm_num)
  have law := sel.represents N n (j+1) hj
  have beta := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed (j+1)))).trans_le law.band.1
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr beta)
  have nonnegative : 0 ≤ motionCost G W.X w := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two hw.le)
  exact W.pure_of_compares B hg hw.le fit
    (rows j hk hj T h t W ψ hψ season (motionCost G W.X w) fee nonnegative hfee price small)

end YM.Integration.FVA1Physical.Wilson
