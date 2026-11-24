import YM.Integration.ActualSignedCore
import YM.Integration.JointSignedInitialization
import YM.MergeProof.Arbol

/-! Replicated Wilson cell estimates from represented arrays. The singletons and
their forced partners are evaluated on the representation at the chosen reading
level. The full coefficient enters the original Wilson partition once. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ReplicatedSignedCellBound
open Finset MeasureTheory Lattice Wilson RG Marker Cells
open MergeProof MergeProof.Accent Extra.Trajectories
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {N p b k : ℕ}

private theorem continuous_copy {n : Side} (T : Tiling n) (i : T.Cell)
    {A : Config G n → ℂ} (hA : Continuous A) : Continuous (T.copy i A) := by
  unfold Tiling.copy
  split_ifs
  · exact (hA.comp (continuous_pull ..)).star
  exact hA.comp (continuous_pull ..)

/-- An actual all-copy coefficient estimate, divided by the number of
reflection cells. The finite-volume exponent becomes a physical mesh ratio. -/
theorem of_served (hC : C.Makes) (hb : b ≤ N) (hk : k ≤ N)
    (A : Config G (C.side N p) → ℂ) (hA : Continuous A)
    (o : Site (C.side b p) → Site (C.side k p))
    (regular : Site (C.side b p) → Config G (C.side k p) → ℂ)
    (forced : Site (C.side b p) → Box (C.side k p) → Config G (C.side k p) → ℂ)
    {w e f x y : ℝ} (hw : 0 < w) (he : 0 ≤ e)
    (served : Served (C.path.rep N p k) regular forced
      (actualJointBirth C (fun i => (center C.S p hb 0).copy i A) hk)
      o (fun _ => w) e f)
    (vault : Vault (fun _ => w) regular forced x y) :
    (center C.S p hb 0).rootTest (C.beta N p) A ≤
      Real.exp ((C.S.a b / C.S.a k) ^ 4 * Vac.treasury C.path.levels k +
        (x + y + 2 * f)) / w := by
  let T := center C.S p hb 0
  let t : Site (C.side b p) → Config G (C.side N p) → ℂ := fun i => T.copy i A
  let B := Stock.census (Site (C.side b p))
  let X (j : ℕ) (hj : j ≤ N) := actualJointBirth C t hj
  have ht (i : Site (C.side b p)) : Continuous (t i) := continuous_copy T i hA
  have hstart : X N le_rfl = birth B (C.path.rep N p N) t :=
    gust_base ..
  have hcont : Continuous (C.path.rep N p N).eval := by
    rw [(hC.wilson.starts N p).2]
    exact bare_cont _
  have htop : Integrable (X N le_rfl) (prior G _) := by
    rw [hstart]
    exact (hatCont C N p t ht hcont B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp := vista C.path B N p k t
    (X := X) (fun j _ hj => gust_step C.path N p N _ hj) hstart htop hC.wilson
    hk (Stock.final (Site (C.side b p)))
    (continuous_integrable _ (continuous_finsetProd _ (fun i _ => ht i)))
    served vault (fun _ => hw) he
  let m := Fintype.card (Site (C.side b p))
  change ‖moment (C.beta N p) (fun U => ∏ i, t i U)‖ *
    (∏ _i : Site (C.side b p), w) ≤ _ at hp
  rw [Finset.prod_const, Finset.card_univ, Stock.tallies C.S b k p] at hp
  unfold Tiling.rootTest
  apply Stock.spacer _ _ w m (norm_nonneg _) hw Fintype.card_pos
  apply hp.trans_eq
  apply congrArg Real.exp
  change (m : ℝ) * _ * _ + m * _ = m * _
  ring

open JointSignedInitialization

/-- The marked source before the complete product and alternative projection.
The two branches share every reflected copy's vacuum and carry independent
root tests. -/
def testedArray {J : Type} [Fintype J] [DecidableEq J] (hb : b ≤ N) (hk : k ≤ N)
    (F : J → Config G (C.side N p) → ℂ) (K : Config G (C.side N p) → ℂ) :=
  let T := center C.S p hb 0
  fun U => JointSignedInitialization.project
    (gust C.path N p N
      (birth JointSignedInitialization.original (C.path.rep N p N)
        (sources (fun c j => T.copy c (F j)) (fun c => T.copy c K))) k hk U)

/-- The paid inputs control the complete signed polynomial obtained by projecting the
jointly propagated numerator. The result is a cell estimate for the literal tested, reflected
product-minus-counterterm on the normalized original Wilson measure. -/
theorem tested_product {J : Type} [Fintype J] [DecidableEq J]
    (hC : C.Makes) (hb : b ≤ N) (hk : k ≤ N)
    (d : J → ℕ) (v : (j : J) → C.label (d j))
    (roots : J → Finset (Site (C.side N p))) (tests : J → Site (C.side N p) → ℂ)
    (D : ℕ) (z : C.label D) (counterRoots : Finset (Site (C.side N p)))
    (counterTest : Site (C.side N p) → ℂ)
    (o : Site (C.side b p) → Site (C.side k p))
    (regular : Site (C.side b p) → Config G (C.side k p) → ℂ)
    (forced : Site (C.side b p) → Box (C.side k p) → Config G (C.side k p) → ℂ)
    {w e f x y : ℝ} (hw : 0 < w) (he : 0 ≤ e)
    (served : Served (C.path.rep N p k) regular forced
      (testedArray hb hk (fun j => column C N p (d j) (v j) (roots j) (tests j))
        (column C N p D z counterRoots counterTest)) o (fun _ => w) e f)
    (vault : Vault (fun _ => w) regular forced x y) :
    (center C.S p hb 0).rootTest (C.beta N p) (fun U =>
      (∏ j, column C N p (d j) (v j) (roots j) (tests j) U) -
        column C N p D z counterRoots counterTest U) ≤
      Real.exp ((C.S.a b / C.S.a k) ^ 4 * Vac.treasury C.path.levels k +
        (x + y + 2 * f)) / w := by
  let F := fun j => column C N p (d j) (v j) (roots j) (tests j)
  let K := column C N p D z counterRoots counterTest
  have source := actual_copied_signed_gust C hC N p (center C.S p hb 0)
    d v roots tests D z counterRoots counterTest hk
  have hsource : actualJointBirth C (fun i => (center C.S p hb 0).copy i
      (fun U => (∏ j, F j U) - K U)) hk = testedArray hb hk F K := source
  have hA : Continuous (fun U => (∏ j, F j U) - K U) :=
    (continuous_finsetProd _ (fun j _ => column_continuous C N p _ _ _ _)).sub
      (column_continuous C N p _ _ _ _)
  exact of_served hC hb hk _ hA o regular forced hw he (hsource ▸ served) vault

end YM.Integration.ReplicatedSignedCellBound
