import YM.Integration.WilsonRunFiniteWickCubature
import YM.Integration.WilsonConditionalTaylorWheelPhysicalSide

/-! An independently filed complete marked polynomial (one source, including
rank zero) is evaluated on the canonical forest of the physical step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelPrimaryFlag
open Function Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open FormalBulk08 Flat Reef Jets Orb Wick Series Next.Free MSbar.Rolling MSbar.Cacao
open Work.F03 Work.F05 Work.F08 PowerSeries Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open WilsonMovingPolynomialPull WilsonConditionalTaylorWick
open scoped Classical Matrix BigOperators
variable {G:Gauge} {K:KernelChoices} {j t:ℕ}

theorem registered {n f:Side} (S:StepData n f) (P:Flight j t) (O:ChartRatio G)
    (law:LocalRatio O) (four:4≤t) (tree:P.patch.Branches K G)
    (hp:S.patch=P.patch) (hk:S.kernel=K) (a:(primary P.patch K n).Choices)
    (row:PoleRows S.patch) (same:HEq row (P.duo K.penalty).A0)
    (U:(b:Side)→Pap (wire G b)) (head:coeff 0 (U (n*P.L))=crunch (kernelP G K.penalty P.wing _)):
    ∃a':S.Choices, HEq a' a ∧ ∀ (T:(b:Side)→Pap (wire G b)) (y:Rays (wire G n)),
      glimpse y (Reef.tossed P O tree (Flat.routes P.patch) n a (U (n*P.L)) (T (n*P.L))) =
        quotient (WilsonMovingFiniteConditional.lift (wire G n) (Pine G S (repeatF S)))
          (Sum.elim (Flat.rawMean G S (repeatF S) (Bloch.installed S.ratio row) *ᵥ y) y)
          (Flat.testPrecision G S (repeatF S) P.wing)⁻¹
          (WilsonMovingFiniteConditional.interaction (Reef.flush (repeatF S) a' O (U f)))
          (Reef.seat (repeatF S) (T f)):=by
  rcases S with ⟨p,k,h⟩
  change p=P.patch at hp
  change k=K at hk
  subst p;subst k
  replace h:f=n*P.patch.L:=Subtype.ext h
  subst f
  obtain rfl:=eq_of_heq same
  let L:=Flat.routes P.patch
  let F:=Reef.floor K P L n
  let H:=Reef.ferry P tree L n
  let B:=Flat.testPrecision G (primary P.patch K n) F P.wing
  refine ⟨a,HEq.rfl,?_⟩
  intro T y
  rw [WilsonConditionalTaylorWheelCanonicalForest.original]
  have funded:=Reef.consolidate P O tree L n law a (U _) head four
  have read:=WilsonMovingFiniteConditional.quotient H y _ (Reef.seat F (T _)) funded
  obtain ⟨bst,paid⟩:=Reef.honey P tree L n
  have inv:B⁻¹=H.saddle.q:=
    left_inv_eq_right_inv (Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr bst.det_pos.ne')) paid
  have drift:WilsonMovingFiniteConditional.mean H y=Sum.elim (Reef.pMean G K P n F *ᵥ y) y:=by
    unfold WilsonMovingFiniteConditional.mean
    rw [← Reef.draught_fee (Reef.pMean G K P n F) y]
    rfl
  rw [←inv,drift] at read
  exact read
end YM.Integration.WilsonConditionalTaylorWheelPrimaryFlag
end
