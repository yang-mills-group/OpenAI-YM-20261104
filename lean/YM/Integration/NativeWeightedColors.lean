import YM.Integration.NativeReplicaServed
import YM.Integration.NativeRestrictionServed

/-!
Exact finite weighted atom aggregation on the full original density.
The native Replica census removes products containing two alternatives of
one original mark.  Its weighted mouth then sums the remaining alternatives.
All coefficient budgets retain their original support headers and price.
No common geometric root or union of atom supports is manufactured here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeWeightedColors
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Trajectories RG3.Annuncia
open JointSignedInitialization Ac
open scoped Classical BigOperators

variable {V W : Type} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] (u : W → V)

/-- Keep exactly the same atoms and exclude repeated original colours. -/
def keep : Names (Replica u (Stock.census V)) (Stock.census W) where
  e := Function.Embedding.refl W
  visible _ := Finset.mem_univ _

def restriction : Poly (Stock.census W) →L[ℂ] Poly (Replica u (Stock.census V)) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := (keep u).restriction
       map_add' := map_add _
       map_smul' := fun c p => (keep u).smul p c } :
      Poly (Stock.census W) →ₗ[ℂ] Poly (Replica u (Stock.census V)))

def fuse (γ : W → ℂ) : Poly (Stock.census W) →L[ℂ] Poly (Stock.census V) :=
  (Replica.cable u (Stock.census V) γ).comp (restriction u)

theorem same_colour_excluded (q : (Replica u (Stock.census V)).Mode)
    {a b : W} (ha : a ∈ q.val) (hb : b ∈ q.val) (he : u a = u b) : a = b :=
  (Replica.admit u (Stock.census V) q).separate ha hb he

theorem fuse_quiet (γ : W → ℂ) (p : Poly (Stock.census W)) :
    (fuse u γ p).part (Stock.census V).quiet = p.part (Stock.census W).quiet := by
  change (Replica.mouth u (Stock.census V) γ ((keep u).restriction p)).part _ = _
  rw [Replica.quiet]
  change p.part ((keep u).share (Replica u (Stock.census V)).quiet) = _
  rw [Names.quiet]

theorem fuse_mach (γ : W → ℂ) (f : W → ℂ) :
    fuse u γ (Mach (Stock.census W) f) =
      Mach (Stock.census V)
        (fun v => ∑ w : W, if v = u w then γ w * f w else 0) := by
  change Replica.mouth u (Stock.census V) γ
    ((keep u).restriction (Mach (Stock.census W) f)) = _
  rw [NativeRestrictionServed.restriction_mach]
  exact Rooted.mouth_mach u (Stock.census V) γ f

theorem fuse_pass (γ : W → ℂ) (p : Poly (Stock.census W))
    (hp : p.part (Stock.census W).quiet = 0) :
    fuse u γ (Poly.pass p) = Poly.pass (fuse u γ p) := by
  change Replica.mouth u (Stock.census V) γ
    ((keep u).restriction (Poly.pass p)) = _
  rw [(keep u).pass_restrict hp]
  apply Replica.passed
  change p.part ((keep u).share (Replica u (Stock.census V)).quiet) = 0
  rw [Names.quiet]
  exact hp

theorem fuse_one (γ : W → ℂ) : fuse u γ 1 = 1 := by
  change Replica.mouth u (Stock.census V) γ ((keep u).restriction 1) = 1
  rw [map_one, map_one]

theorem fuse_mul (γ : W → ℂ) (p q : Poly (Stock.census W)) :
    fuse u γ (p * q) = fuse u γ p * fuse u γ q := by
  change Replica.mouth u (Stock.census V) γ ((keep u).restriction (p * q)) = _
  rw [map_mul, map_mul]
  rfl

theorem fuse_prod (γ : W → ℂ) {A : Type} (s : Finset A)
    (f : A → Poly (Stock.census W)) :
    fuse u γ (∏ i ∈ s, f i) = ∏ i ∈ s, fuse u γ (f i) := by
  change Replica.mouth u (Stock.census V) γ ((keep u).restriction (∏ i ∈ s, f i)) = _
  rw [map_prod, map_prod]
  rfl

theorem fuse_bead (γ : W → ℂ) (c : ℂ) :
    fuse u γ (Poly.bead (Stock.census W) c) = Poly.bead (Stock.census V) c := by
  change Replica.mouth u (Stock.census V) γ
    ((keep u).restriction (Poly.send (Stock.census W).quiet c)) = _
  have hr : (keep u).restriction (Poly.send (Stock.census W).quiet c) =
      Poly.send (Replica u (Stock.census V)).quiet c := by
    apply Marker.Poly.ext
    intro q
    change (Poly.send (Stock.census W).quiet c).part ((keep u).share q) = _
    rw [Poly.part_send, Poly.part_send, ← (keep u).quiet]
    simp only [(keep u).inj.eq_iff]
  rw [hr, Replica.single]
  rfl

variable {G : Gauge} {n : Side}

theorem fuse_field (γ : W → ℂ) (f : Box n → Poly (Stock.census W))
    (s : Support n) :
    fuse u γ (field f s) = field (fun i => fuse u γ (f i)) s := by
  unfold field
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold grid
  split
  · exact fuse_prod u γ _ _
  exact map_zero _

/-- The complete one-vacuum birth, with the original weighted fibre sums. -/
theorem fuse_birth (γ : W → ℂ) (P : Rep G n)
    (F : W → Config G n → ℂ) :
    (fun U => fuse u γ (birth (Stock.census W) P F U)) =
      birth (Stock.census V) P (Rooted.aggregate u γ F) := by
  funext U
  unfold birth
  rw [map_smul, fuse_pass u γ _ (mute _ _), fuse_mach]
  rfl

/-- The same full polynomial map commutes with the actual history push. -/
theorem fuse_gust (γ : W → ℂ) (H : History G) (N p j : ℕ)
    (P : Config G (H.S.side j p) → Poly (Stock.census W))
    (hP : Integrable P (prior G (H.S.side j p))) {m : ℕ} (hm : m ≤ j) :
    gust H N p j (fun U => fuse u γ (P U)) m hm =
      fun U => fuse u γ (gust H N p j P m hm U) := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i hi ih =>
      rw [gust_step H N p j _ hi, ih]
      funext U
      rw [gust_step H N p j P hi]
      unfold StepData.push
      let L := (fuse u γ).restrictScalars ℝ
      have he := L.integral_comp_comm
        (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i + 1)))
          U _ (gust_live H N p j P hP hi))
      simp_rw [L.map_smul] at he
      exact he

/-- One coefficient envelope precedes every bounded independent atom weight.
The support map and complete price are unchanged; no atom-count factor occurs. -/
theorem common_envelope {A Y : Type} (w : V → ℝ) (a : W → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    {X : A → Support n} {F : A → Y → Poly (Stock.census W)}
    {b : ℕ} {e c : ℝ}
    (h : Towed (fun i => a i * w (u i)) X F b e c) :
    ∃ q : A → (Stock.census V).Mode → ℝ,
      Summable (fun i => RG3.Riding.unitPrice (Stock.census V) w (q i)) ∧
      Hit X b (fun i => RG3.Riding.unitPrice (Stock.census V) w (q i)) e c ∧
      ∀ i, 0 ≤ q i ∧ ∀ γ : W → ℂ, (∀ j, ‖γ j‖ ≤ a j) →
        ∀ U s, ‖(fuse u γ (F i U)).part s‖ ≤ q i s := by
  have hr : Towed (fun i => a i * w (u i)) X
      (fun i U => (keep u).restriction (F i U)) b e c :=
    NativeRestrictionServed.restriction_towed (keep u)
      (fun i => a i * w (u i)) (fun i => mul_nonneg (ha i) (hw (u i))) h
  let Γ := {γ : W → ℂ // ∀ i, ‖γ i‖ ≤ a i}
  obtain ⟨q, hq, hHit, hBound⟩ := Replica.save u (Stock.census V) w a hw
    (fun γ : Γ => γ.val) (fun γ => γ.property) ha hr
  exact ⟨q, hq, hHit, fun i => ⟨(hBound i).1,
    fun γ hγ U s => (hBound i).2 ⟨γ, hγ⟩ U s⟩⟩

end YM.Integration.NativeWeightedColors
