import YM.RG05Readout.Flatten.Joints
import YM.Integration.RootedJointSignedInitialization

/-!
The literal RG05 clinic as a finite weighted source of the original physical
family.  Every fine preimage and every palette coordinate is retained.  The
terminal map and engineering power are explicit; no point field is silently
identified with a threshold-normalized stencil.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRG05PhysicalSource
open Function Finset MeasureTheory Lattice Wilson RG Source Marker
open Extra.Histories MergeProof MergeProof.Accent
open Push Extra.Trajectories MergeProof.Ribbons RG3.Annuncia
open RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Records RG05Readout.Records.Basket RG05Readout.Flatten
open scoped BigOperators Classical Topology

variable {G : Gauge} (C : Family G)

/-- The original factory terminal map, at the actual cutoff and period. -/
def atomLabel (N p d : ℕ) (b : Mark C d) : C.label (kept b.1) :=
  (C.factory (kept b.1) N p).terminal
    (Size.axis (C.labels.level (kept b.1)) b.2)

/-- The engineering factor omitted by the native threshold stencil. -/
def atomScale (N d : ℕ) (b : Mark C d) : ℂ :=
  (C.S.a N : ℂ) ^ kept b.1

theorem presented_physical (hC : C.Makes) (N p d : ℕ)
    (v : C.label d) (o : Site (C.side N p)) :
    Local.presented (C.localSection d) o (C.path.rep N p N).p.threshold v =
      (C.S.a N : ℂ) ^ d •
        C.O N p ((C.factory d N p).terminal v) o := by
  have ht : (C.path.rep N p N).p.threshold = C.path.levels.clock.threshold N := by
    rw [(hC.wilson.represents N p N le_rfl).vac]
    rfl
  have hs : (C.S.a N : ℂ) ^ d ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')
  funext U
  simp only [Local.presented, LinearMap.coe_mk, AddHom.coe_mk, ht,
    Family.O, TransferData.cylinder, LinearEquiv.symm_apply_apply,
    initial, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem identity_motion (N p d : ℕ) (v : C.label d)
    (o : Site (C.side N p)) :
    stepUp (1, false) o (C.O N p v 0) = C.O N p v o := by
  funext U
  unfold stepUp
  dsimp only
  rw [pull_one]
  change C.O N p v 0 (Lattice.translate o U) = _
  simpa only [zero_add] using C.translation 0 o v U

theorem motion_physical (N p d : ℕ) (v : C.label d)
    (t : Motion) (o x : Site (C.side N p)) :
    stepUp t o (C.O N p v x) =
      stepUp t (affine t.1 o x) (C.O N p v 0) := by
  rw [← identity_motion C N p d v x, RG05Readout.View.step_cycle]
  simp only [MergeProof.twist, mul_one, Bool.xor_false]

theorem entrance_physical (hC : C.Makes) (N p d : ℕ)
    (v : Palette C d) (o : Site (C.side N p)) (φ : Body) :
    entrance C d N p v o φ =
      ∑ b : Mark C d,
        (val v b * readJ b.1 0 φ * atomScale C N d b) •
          C.O N p (atomLabel C N p d b) o := by
  unfold entrance
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [presented_physical C hC]
  simp only [smul_smul, atomScale, atomLabel, mul_assoc]

/-- The complete coefficient of one original fine preimage and palette atom. -/
def clinicWeight (N p d n : ℕ) (h : n ≤ N) (v : Palette C d) (φ : Body)
    (x : Site (C.S.toDepth h p).count) (b : Mark C d) : ℂ :=
  ratioX (C.S.toDepth h p) d *
    (val v b * readJ b.1 0 (feeR (C.S.toDepth h p) x φ) * atomScale C N d b)

theorem clinic_identity (hC : C.Makes) (N p d n : ℕ) (h : n ≤ N)
    (v : Palette C d) (o : Site (C.side n p)) (φ : Body) :
    clinic C p N d v n o (1, false) φ =
      ∑ x : Site (C.S.toDepth h p).count, ∑ b : Mark C d,
        clinicWeight C N p d n h v φ x b •
          C.O N p (atomLabel C N p d b) ((C.S.toDepth h p).assemble (o, x)) := by
  unfold clinic
  rw [lift_pol (hm := le_refl N) (ht := h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [like_embed]
  change ratioX (C.S.toDepth h p) d •
    stepUp (1, false) ((C.S.toDepth h p).assemble (o, x))
      (entrance C d N p v 0 (feeR (C.S.toDepth h p) x φ)) = _
  rw [entrance_physical C hC, Records.rot_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Records.rot_scalar, identity_motion C N p]
  change ratioX (C.S.toDepth h p) d •
    ((val v b * readJ b.1 0 (feeR (C.S.toDepth h p) x φ) * atomScale C N d b) •
      C.O N p (atomLabel C N p d b) ((C.S.toDepth h p).assemble (o, x))) = _
  rw [smul_smul]
  rfl

/-- All reflected/rotated preimages, with the scalar action on each weight. -/
theorem clinic_motion (hC : C.Makes) (N p d n : ℕ) (h : n ≤ N)
    (v : Palette C d) (o : Site (C.side n p)) (t : Motion) (φ : Body) :
    clinic C p N d v n o t φ =
      ∑ x : Site (C.S.toDepth h p).count, ∑ b : Mark C d,
        Motion.scalar t (clinicWeight C N p d n h v φ x b) •
          stepUp t (affine t.1 ((C.S.toDepth h p).embed o)
            ((C.S.toDepth h p).assemble (0, x)))
            (C.O N p (atomLabel C N p d b) 0) := by
  have hz : clinic C p N d v n o t φ =
      stepUp t ((C.S.toDepth h p).embed o)
        (clinic C p N d v n 0 (1, false) φ) := by
    unfold clinic uniform
    rw [dif_pos h, dif_pos h]
    rw [show (C.S.toDepth h p).embed 0 = 0 from (C.S.toDepth h p).root.map_zero]
    rw [stepid]
  rw [hz, clinic_identity C hC, Records.rot_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Records.rot_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Records.rot_scalar, motion_physical C N p]

section Array
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every preimage is retained independently for every original logical slot. -/
abbrev Atom (N p n : ℕ) (h : n ≤ N) (d : V → ℕ) :=
  (i : V) × (Site (C.S.toDepth h p).count × Mark C (d i))

def weights (N p n : ℕ) (h : n ≤ N) (d : V → ℕ) (t : V → Motion)
    (v : (i : V) → Palette C (d i)) (φ : V → Body)
    (a : Atom C N p n h d) : ℂ :=
  Motion.scalar (t a.1)
    (clinicWeight C N p (d a.1) n h (v a.1) (φ a.1) a.2.1 a.2.2)

/-- The physical fields are fixed before the palette coefficients and tests. -/
def atoms (N p n : ℕ) (h : n ≤ N) (d : V → ℕ)
    (o : V → Site (C.side n p)) (t : V → Motion)
    (a : Atom C N p n h d) : Config G (C.side N p) → ℂ :=
  stepUp (t a.1)
    (affine (t a.1).1 ((C.S.toDepth h p).embed (o a.1))
      ((C.S.toDepth h p).assemble (0, a.2.1)))
    (C.O N p (atomLabel C N p (d a.1) a.2.2) 0)

private theorem aggregate_sigma {A : V → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] {X : Type} (γ : ((i : V) × A i) → ℂ)
    (f : ((i : V) × A i) → X → ℂ) (i : V) (U : X) :
    JointSignedInitialization.Rooted.aggregate Sigma.fst γ f i U =
      ∑ a : A i, γ ⟨i, a⟩ * f ⟨i, a⟩ U := by
  unfold JointSignedInitialization.Rooted.aggregate
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [ite_true]
  · intro j _ hj
    simp only [if_neg (Ne.symm hj), Finset.sum_const_zero]
  · simp

theorem aggregate_clinics (hC : C.Makes) (N p n : ℕ) (h : n ≤ N)
    (d : V → ℕ) (o : V → Site (C.side n p)) (t : V → Motion)
    (v : (i : V) → Palette C (d i)) (φ : V → Body) :
    JointSignedInitialization.Rooted.aggregate Sigma.fst
      (weights C N p n h d t v φ) (atoms C N p n h d o t) =
        fun i => clinic C p N (d i) (v i) n (o i) (t i) (φ i) := by
  funext i U
  rw [aggregate_sigma, Fintype.sum_prod_type,
    clinic_motion C hC N p (d i) n h (v i) (o i) (t i) (φ i)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, weights, atoms]

/-- One original-vacuum polynomial, chosen before every independent test. -/
def oneVacuumSource (N p n : ℕ) (h : n ≤ N) (d : V → ℕ)
    (o : V → Site (C.side n p)) (t : V → Motion) (B : Census V) :=
  Accent.birth (Replica (Sigma.fst : Atom C N p n h d → V) B)
    (C.path.rep N p N) (atoms C N p n h d o t)

theorem source_integrable (hC : C.Makes) (N p n : ℕ) (h : n ≤ N)
    (d : V → ℕ) (o : V → Site (C.side n p)) (t : V → Motion)
    (B : Census V) :
    Integrable (oneVacuumSource C N p n h d o t B)
      (prior G (C.side N p)) := by
  have ha (a : Atom C N p n h d) : Continuous (atoms C N p n h d o t a) := by
    unfold atoms stepUp Motion.scalar
    split
    · exact ((C.continuousO N p _ _ 0).comp (continuous_pull ..)).star
    · exact (C.continuousO N p _ _ 0).comp (continuous_pull ..)
  have hP : Continuous (C.path.rep N p N).eval := by
    rw [(hC.wilson.starts N p).2]
    exact bare_cont _
  exact (hatCont C N p _ ha hP _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem clinic_birth (hC : C.Makes) (N p n : ℕ) (h : n ≤ N)
    (d : V → ℕ) (o : V → Site (C.side n p)) (t : V → Motion)
    (B : Census V) (v : (i : V) → Palette C (d i)) (φ : V → Body) :
    (fun U => Replica.mouth Sigma.fst B (weights C N p n h d t v φ)
      (oneVacuumSource C N p n h d o t B U)) =
        Accent.birth B (C.path.rep N p N)
          (fun i => clinic C p N (d i) (v i) n (o i) (t i) (φ i)) := by
  unfold oneVacuumSource
  rw [JointSignedInitialization.Rooted.mouth_birth,
    aggregate_clinics C hC]

/-- Exact actual propagation of the entire weighted clinic array.  Its
source and vacuum do not depend on the independent profile choices. -/
theorem clinic_gust (hC : C.Makes) (N p n : ℕ) (h : n ≤ N)
    (d : V → ℕ) (o : V → Site (C.side n p)) (t : V → Motion)
    (B : Census V) (v : (i : V) → Palette C (d i)) (φ : V → Body)
    {m : ℕ} (hm : m ≤ N) :
    gust C.path N p N (Accent.birth B (C.path.rep N p N)
      (fun i => clinic C p N (d i) (v i) n (o i) (t i) (φ i))) m hm =
        fun U => Replica.mouth Sigma.fst B (weights C N p n h d t v φ)
          (gust C.path N p N (oneVacuumSource C N p n h d o t B) m hm U) := by
  rw [← clinic_birth C hC N p n h d o t B v φ]
  exact JointSignedInitialization.Rooted.mouth_gust Sigma.fst B
    (weights C N p n h d t v φ) C.path N p
    (oneVacuumSource C N p n h d o t B)
    (source_integrable C hC N p n h d o t B) hm

end Array

end YM.Integration.ActualRG05PhysicalSource
