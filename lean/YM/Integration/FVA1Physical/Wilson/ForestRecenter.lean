import YM.Integration.FVA1Physical.Wilson.PostureReadout
import YM.MSbar.Atlas.Epoch

/-! The complete tracked-motion comparison on the same independently selected
Wilson scene at every retained stage. An admissible cell contains only native
physical window data and scalar localization parameters. It contains no
identification of actual and formal coefficients. -/
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
variable {G:Gauge} {f c:Side}

structure ForestCell (S : StepData c f) (R : Rep G f) (out : Rep G c) where
  F : Forest S.ratio
  X : Support f
  Y : Support f
  J : Voice G
  P : Palisade
  x : Positions (Primary c G)
  center : Positions (Key F G)
  a : ℝ
  b : ℝ
  threshold : ℝ
  bound : ℝ
  M : ℕ
  d : ℕ
  radius : ℝ
  register : ℕ
  source : S.Choices
  voice : Clear G J
  posture : Posture P J F a b threshold bound M d X Y x center R.p
  covered : threshold ≤ out.p.threshold
  grant : Grants source R F P register
  radius_le : radius ≤ 1
  garden : Posture.gardenCity P J bound radius b

variable {Q : StepData c f} {R : Rep G f} {out : Rep G c}

/-- Normalized error against the independent bank for every native locally
measurable test and every finite angular change of the recorded forest. -/
def ForestCell.Compares (W : ForestCell Q R out) (B : Positions (Primary f G)→ℝ)
    (g w ε H fee C σ δ Λ forced ψ : ℝ) : Prop :=
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
    |(Q.push R.beta (fun U=>q U*(R.eval (κ U)*Real.exp (moveBank R copy κ B g w H U)) ) O -
        Q.push R.beta (fun U=>q U*R.eval U) O)/Z| ≤ charge+2*(H*(ε/w)+fee)*(ζ*b+charge)

variable {C : Family G} (L : Bulk.Chain C.path)

theorem inherited_forest_readout (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
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
          ∀ H fee, 0 ≤ H → 0 ≤ fee →
          silkRoad pred.paths pred.width (cal.allowance (j+1)) (cal.loopCap (j+1)) R.beta W.X.card W.M R.p W.d ≤ fee →
          H*(ε/w)+fee ≤ 1 → W.Compares B g w ε H fee pred.paths pred.width
            (cal.allowance (j+1)) (cal.loopCap (j+1)) (cal.forcedAllowance (j+1)) ψ := by
  have high := Multi.Wage.hat_tend simple C.path.levels
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp ((Alto.broad.comp high).eventually_gt_atTop 0)
  filter_upwards [uniform_patch_oscillation L u simple sel D s p m hs hm hp hη,eventually_ge_atTop k₀] with k bought cutoff
  intro N n lo
  obtain ⟨S,hS,rows⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hk hj T h t R out S' cal g w pred B ε W ψ hψ season H fee hH hfee spend small
  have jk := hk.trans (Nat.le_succ j)
  have hw : 0 < w := div_pos (h₀ _ (cutoff.trans jk)) (by norm_num)
  have law := sel.represents N n (j+1) hj
  have beta := (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed (j+1)))).trans_le law.band.1
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr beta)
  let O := represent (tint G (Exterior.Body 1 (C.side j n)) W.x)
  have mass : 0 < S'.push R.beta R.eval O := by
    rw [←season.taskEval]
    exact SectorNext.Vacuum.strictly C.path sel N n j hj.le O
  have adm : Admitted O R S' pred.width pred.paths (cal.allowance (j+1)) (cal.loopCap (j+1)) (cal.forcedAllowance (j+1)) :=
    ⟨law.good,fun U=>(season.shine U).le,mass,S'.isKernel season.bends.1 _⟩
  intro angle φ localφ φ₀ b φB
  exact posture_wilson_readout W.F W.X W.Y W.J W.P W.x W.center W.voice W.posture W.source W.grant adm
    season.shine season.bends.1 season.case_.decent beta.le W.radius_le W.garden season.primal season.storm
    W.covered hψ B (continuous_bank L S T hj h t hS jk p (Nat.le_succ p) g) hg.ne' hw (Real.rpow_nonneg hg.le _)
    hH hfee spend small (rows (j+1) jk hj T h t) angle φ localφ φ₀ φB

end YM.Integration.FVA1Physical.Wilson
