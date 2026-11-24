import YM.Integration.WilsonRunVacuumWickCubature

/-! Evaluate the entire independently selected nonlinear input, before
any period or forest is chosen. Only its true quadratic head is used
to open the independent finite Gaussian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMutableVacuumWickCubature
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Bank Dawn Rial Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorWick WilsonMovingPolynomialPull WilsonMovingIndependentWick
open scoped Classical BigOperators Matrix

open WilsonRunVacuumWickCubature
variable {G : Gauge} {K : KernelChoices} {j t : ℕ}

def opening (P : Flight j t) (L : Lodge P.patch) (O : ChartRatio G)
    (b : P.patch.Branches K G) (n : Side) (a : (primary P.patch K n).Choices)
    (p : Pap (wire G (n*P.L))) (y : Rays (wire G n)) :=
  let H := Reef.ferry P b L n
  contract (WilsonMovingFiniteConditional.lift (wire G n) _) (WilsonMovingFiniteConditional.mean H y) H.saddle.q
    (Spring (WilsonMovingFiniteConditional.interaction (Reef.flush (Reef.floor K P L n) a O p)))

theorem carry {n f : Side} (S : StepData n f) (P : Flight j t) (L : Lodge P.patch)
    (O : ChartRatio G) (b : P.patch.Branches K G) (hp : S.patch=P.patch) (hk : S.kernel=K)
    (row : PoleRows S.patch) (same : HEq row (P.duo K.penalty).A0) (a : (primary P.patch K n).Choices) :
    ∃ (F : Forest S.ratio) (a' : S.Choices), HEq F (Reef.floor K P L n) ∧ HEq a' a ∧
      ∀ (U : (v : Side) → Pap (wire G v)) (y : Rays (wire G n)),
        opening P L O b n a (U (n*P.L)) y =
        contract (WilsonMovingFiniteConditional.lift (wire G n) (Pine G S F))
          (Sum.elim (Flat.rawMean G S F (Bloch.installed S.ratio row) *ᵥ y) y)
          (Flat.testPrecision G S F P.wing)⁻¹
          (Spring (WilsonMovingFiniteConditional.interaction (Reef.flush F a' O (U f)))) := by
  rcases S with ⟨p,k,hs⟩
  change p=P.patch at hp
  change k=K at hk
  subst p
  subst k
  have hs' : f=n*P.patch.L := Subtype.ext hs
  subst f
  obtain rfl := eq_of_heq same
  let F := Reef.floor K P L n
  let H := Reef.ferry P b L n
  let B := Flat.testPrecision G (primary P.patch K n) F P.wing
  obtain ⟨bst,paid⟩ := Reef.honey P b L n
  have inv : B⁻¹ = H.saddle.q :=
    left_inv_eq_right_inv (Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr bst.det_pos.ne')) paid
  refine ⟨F,a,HEq.rfl,HEq.rfl,?_⟩
  intro U y
  have drift : WilsonMovingFiniteConditional.mean H y =
      Sum.elim (Reef.pMean G K P n F *ᵥ y) y := by
    unfold WilsonMovingFiniteConditional.mean
    rw [← Reef.draught_fee (Reef.pMean G K P n F) y]
    rfl
  change contract _ (WilsonMovingFiniteConditional.mean H y) H.saddle.q _ =
    contract _ (Sum.elim (Reef.pMean G K P n F *ᵥ y) y) B⁻¹ _
  rw [← inv,drift]
  rfl

variable (R : Run G) (N i per : ℕ) (hi : i<N)
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)

theorem filed (roofs : ∀ k, Lodge ((R.family.path.levels.clock.op k 0).patch))
    (U : (n : Side)→Pap (wire G n))
    (head : coeff 0 (U ((R.family.S.side i per) * (destination R.family.path.levels N i).L)) =
      crunch (kernelP G R.family.path.levels.clock.kernel.penalty (destination R.family.path.levels N i).wing
        ((R.family.S.side i per) * (destination R.family.path.levels N i).L))) :
    let V := R.family.path.levels
    let S := V.clock.op i per
    let P := destination V N i
    let b := fun k => (V.blocks k 0).branches
    let n := R.family.S.side i per
    let fine := R.family.S.side (i+1) per
    let H := Reef.ferry P (b i) (roofs i) n
    let Y := Reef.landed P R.metals.O (b i) (roofs i) n tag (U (n*P.L))
    ∃ (F : Forest S.ratio) (t : S.Choices),
      HEq F (Reef.floor V.clock.kernel P (roofs i) n) ∧ HEq t tag ∧ ∀ u : Positions (Primary n G),
        let y := FreeResolvent.flatten (tint G (Body 1 n) u)
        glimpse y Y = PowerSeries.C (traceP y H.main) +
          covelog (bank ((RunFormalChain.fromRun R).step N i per hi) F t u (U fine)) := by
  intro V S P b n fine H Y
  obtain ⟨F,t,hF,ht,charged⟩ := carry S P (roofs i) R.metals.O (b i) rfl rfl
    (P.duo V.clock.kernel.penalty).A0 HEq.rfl tag
  refine ⟨F,t,hF,ht,?_⟩
  intro u y
  have solved := Reef.consolidate P R.metals.O (b i) (roofs i) n R.alloy.B.ratio tag (U _)
    head (V.clock.adm i)
  have deposited := formal H y _ solved
  change glimpse y Y = PowerSeries.C (traceP y H.main) +
    covelog (opening P (roofs i) R.metals.O (b i) n tag (U (n*P.L)) y) at deposited
  rw [deposited,charged U y, measured R N i per hi F t u (U fine)]

end YM.Integration.WilsonMutableVacuumWickCubature
end
