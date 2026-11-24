import YM.Integration.WilsonRunFiniteWickCubature
import YM.Integration.WilsonMovingRunWickCoordinates

/-! The original physical conditional Wick program, with its own covariance,
affine shift, field ordering, kernel and chart ratio, receives the *complete*
independently filed cubature on that same finite run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRunMeasuredWickCubature
open Function Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Jets Orb Wick Series Next.Free MSbar.Rolling MSbar.Cacao
open Work.F03 Work.F05 Work.F08 PowerSeries Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels
open WilsonMovingPolynomialPull WilsonConditionalTaylorWick
open scoped Classical Matrix BigOperators
variable {G : Gauge} {K : KernelChoices} {j t : ℕ}

def reading {c f : Side} {S : StepData c f} {p : Clip} {X : PathData G} {O : ChartRatio G}
    (K₀ : Bulk.Kernel S p X O) (F : Forest S.ratio) (a : S.Choices)
    (u : Positions (Primary c G)) (U T : Pap (wire G f)) :=
  quotient (straight F G) (poring F (K₀.b F) *ᵥ u) (K₀.covariance F a)
    (barbed F a O (splitV (place (WilsonMovingGaussianCoordinates.link G f).symm U)))
    (PowerSeries.map (rail (taps F G)).toRingHom (place (WilsonMovingGaussianCoordinates.link G f).symm T))

private def independent (P : Flight j t) (L : Lodge P.patch) (O : ChartRatio G)
    (bs : P.patch.Branches K G) (n : Side) (a : (primary P.patch K n).Choices)
    (U T : Pap (wire G (n*P.L))) (y : Rays (wire G n)) :=
  let F := Reef.floor K P L n
  let H := Reef.ferry P bs L n
  quotient (WilsonMovingFiniteConditional.lift (wire G n) _) (WilsonMovingFiniteConditional.mean H y)
    H.saddle.q (WilsonMovingFiniteConditional.interaction (Reef.flush F a O U)) (Reef.seat F T)

private theorem carry {n f : Side} (S : StepData n f) (P : Flight j t) (L : Lodge P.patch)
    (O : ChartRatio G) (bs : P.patch.Branches K G) (hp : S.patch=P.patch) (hk : S.kernel=K)
    (row : PoleRows S.patch) (same : HEq row (P.duo K.penalty).A0) (a : (primary P.patch K n).Choices) :
    ∃ (F : Forest S.ratio) (a' : S.Choices), HEq F (Reef.floor K P L n) ∧ HEq a' a ∧
      ∀ (U T : (v : Side) → Pap (wire G v)) (y : Rays (wire G n)),
        independent P L O bs n a (U (n*P.L)) (T (n*P.L)) y =
        quotient (WilsonMovingFiniteConditional.lift (wire G n) (Pine G S F))
          (Sum.elim (Flat.rawMean G S F (Bloch.installed S.ratio row) *ᵥ y) y)
          (Flat.testPrecision G S F P.wing)⁻¹
          (WilsonMovingFiniteConditional.interaction (Reef.flush F a' O (U f))) (Reef.seat F (T f)) := by
  rcases S with ⟨p,k,hs⟩
  change p=P.patch at hp
  change k=K at hk
  subst p
  subst k
  have hs' : f=n*P.patch.L := Subtype.ext hs
  subst f
  obtain rfl := eq_of_heq same
  let F := Reef.floor K P L n
  let H := Reef.ferry P bs L n
  let B := Flat.testPrecision G (primary P.patch K n) F P.wing
  obtain ⟨bst,paid⟩ := Reef.honey P bs L n
  have inv : B⁻¹ = H.saddle.q :=
    left_inv_eq_right_inv (Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr bst.det_pos.ne')) paid
  refine ⟨F,a,HEq.rfl,HEq.rfl,?_⟩
  intro U T y
  have drift : WilsonMovingFiniteConditional.mean H y =
      Sum.elim (Reef.pMean G K P n F *ᵥ y) y := by
    unfold WilsonMovingFiniteConditional.mean
    rw [← Reef.draught_fee (Reef.pMean G K P n F) y]
    rfl
  change quotient _ (WilsonMovingFiniteConditional.mean H y) H.saddle.q _ _ =
    quotient _ (Sum.elim (Reef.pMean G K P n F *ᵥ y) y) B⁻¹ _ _
  rw [← inv,drift]
  rfl

variable {d e : ℕ} (R : Run G) (roofs : ∀ k, Lodge ((R.family.path.levels.clock.op k 0).patch))
    (a : hue G) (fit : d<e)

theorem filed (simple : G.Simple) (N i per : ℕ) (hi : i<N)
    (z : Letter (R.family.labels.level d)) (l : ℕ) (f : Dawn.Studio e)
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let V := R.family.path.levels
    let S := V.clock.op i per
    let P := destination V N i
    let bs := fun k => (V.blocks k 0).branches
    let W := Dove.model V roofs bs R.metals.O a N (i+1)
    let Y := (WilsonRunFormalMarkedStep.graph R roofs a fit N (i+1)) z
    let n := R.family.S.side i per
    let fine := R.family.S.side (i+1) per
    let block := Elm.growL V i
    let T := fun (x : Site P.L) (v : Side) => Kemp.resite (wrap v (lift x)) (Kemp.banner l (Y (Dawn.throughW x e block f)) v)
    ∃ (F : Forest S.ratio) (t : S.Choices),
      HEq F (Reef.floor V.clock.kernel P (roofs i) n) ∧ HEq t tag ∧ ∀ u : Positions (Primary n G),
        glimpse (FreeResolvent.flatten (tint G (Body 1 n) u))
          (WilsonFormalMarkedCubature.finiteTransfer P (roofs i) W R.metals.O (bs i) block Y d l f n tag) =
        PowerSeries.C (Kemp.aven P.L d) * ∑ x : Site P.L,
          reading ((RunFormalChain.fromRun R).step N i per hi) F t u (Mesa.stone W fine) (T x fine) := by
  intro V S P bs W Y n fine block T
  obtain ⟨F,t,hF,ht,charged⟩ := carry S P (roofs i) R.metals.O (bs i) rfl rfl
    (P.duo V.clock.kernel.penalty).A0 HEq.rfl tag
  refine ⟨F,t,hF,ht,?_⟩
  intro u
  let y := FreeResolvent.flatten (tint G (Body 1 n) u)
  rw [WilsonRunFiniteWickCubature.onRun R roofs a fit simple N i per hi z l f tag y]
  change PowerSeries.C (Kemp.aven P.L d) * (∑ x : Site P.L, independent P (roofs i) R.metals.O
    (bs i) n tag (Mesa.stone W (n*P.L)) (T x (n*P.L)) y) = _
  apply congrArg (fun v : PowerSeries ℝ => PowerSeries.C (Kemp.aven P.L d)*v)
  apply Finset.sum_congr rfl
  intro x hx
  exact (charged (Mesa.stone W) (T x) y).trans
    (WilsonMovingRunWickCoordinates.source R N i per hi F t u (Mesa.stone W fine) (T x fine))

end YM.Integration.WilsonRunMeasuredWickCubature
end
