import YM.Integration.ActualRG05PhysicalSource

/-!
The original RG05 clinic atoms as native threshold stencils at their own
fine origins.  Motion acts on the complete coefficient vector, and the
engineering factor is transferred exactly from the physical field to its
coefficient.  No origins, supports or vacuum are changed.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRG05NativeAtoms
open Function Finset Lattice Wilson RG Source Labels Marker
open Extra.Histories MergeProof Push.Local
open RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Records RG05Readout.Records.Basket RG05Readout.Flatten
open ActualRG05PhysicalSource
open scoped Classical BigOperators

variable {G : Gauge}

theorem presented_motion {n : Side} {d : ℕ} {F : Frame G d}
    (T : SectionData F) {H : Hol G} (hT : T.Sound H)
    (t : Motion) (o x : Site n) (ε : ℝ) (v : F.Coeff) :
    stepUp t x (presented T o ε v) =
      presented T (affine t.1 x o) ε (Motion.patch F t v) := by
  funext U
  change Motion.scalar t (T.places (F.scaled ε⁻¹ v) o (pull t.1 x U)) =
    T.places (F.scaled ε⁻¹ (Motion.patch F t v)) (affine t.1 x o) U
  rw [T.placed_signed hT]
  unfold Motion.scalar Motion.patch
  split
  · rw [scaled_star, F.scaling]
    exact (hT.ordinary_real _ _).symm
  rw [F.scaling]

variable (C : Family G)

def nativeLabel (d : ℕ) (t : Motion) (b : Mark C d) : C.label (kept b.1) :=
  Motion.patch (C.labels.level (kept b.1)) t
    (Size.axis (C.labels.level (kept b.1)) b.2)

theorem label_price (d : ℕ) (t : Motion) (b : Mark C d) :
    (C.labels.level (kept b.1)).coeffSize (nativeLabel C d t b) ≤
      Motion.orbitCost (C.labels.level (kept b.1)) *
        (C.labels.level (kept b.1)).coeffSize
          (Size.axis (C.labels.level (kept b.1)) b.2) :=
  Motion.patch_cost _ _ _

theorem scale_fixed (L d : ℕ) (t : Motion) (b : Mark C d) :
    Motion.scalar t (atomScale C L d b) = atomScale C L d b := by
  unfold atomScale
  rw [← Complex.ofReal_pow]
  exact Motion.scalar_real _ _

theorem native_atom (hC : C.Makes) (L p d : ℕ) (t : Motion)
    (b : Mark C d) (x : Site (C.side L p)) :
    atomScale C L d b • stepUp t x (C.O L p (atomLabel C L p d b) 0) =
      presented (C.localSection (kept b.1)) x
        (C.path.rep L p L).p.threshold (nativeLabel C d t b) := by
  calc
    _ = stepUp t x (atomScale C L d b •
        C.O L p (atomLabel C L p d b) 0) := by
      rw [Records.rot_scalar, scale_fixed]
    _ = stepUp t x (presented (C.localSection (kept b.1)) 0
        (C.path.rep L p L).p.threshold
        (Size.axis (C.labels.level (kept b.1)) b.2)) := by
      rw [presented_physical C hC]
      rfl
    _ = _ := by
      simpa only [nativeLabel, affine, Signed.act_zero, zero_add] using
        presented_motion (C.localSection (kept b.1)) (hC.sections (kept b.1))
          t 0 x (C.path.rep L p L).p.threshold
          (Size.axis (C.labels.level (kept b.1)) b.2)

def amplitude (L p d n : ℕ) (h : n ≤ L) (t : Motion)
    (v : Palette C d) (φ : Body) (x : Site (C.S.toDepth h p).count)
    (b : Mark C d) : ℂ :=
  Motion.scalar t (ratioX (C.S.toDepth h p) d *
    (val v b * readJ b.1 0 (feeR (C.S.toDepth h p) x φ)))

theorem weight_factor (L p d n : ℕ) (h : n ≤ L) (t : Motion)
    (v : Palette C d) (φ : Body) (x : Site (C.S.toDepth h p).count)
    (b : Mark C d) :
    Motion.scalar t (clinicWeight C L p d n h v φ x b) =
      amplitude C L p d n h t v φ x b * atomScale C L d b := by
  unfold clinicWeight amplitude
  rw [← mul_assoc, Motion.scalar_mul, scale_fixed]

theorem amplitude_norm (L p d n : ℕ) (h : n ≤ L) (t : Motion)
    (v : Palette C d) (φ : Body) (x : Site (C.S.toDepth h p).count)
    (b : Mark C d) :
    ‖amplitude C L p d n h t v φ x b‖ =
      ‖ratioX (C.S.toDepth h p) d‖ *
        (‖val v b‖ * ‖readJ b.1 0 (feeR (C.S.toDepth h p) x φ)‖) := by
  simp only [amplitude, Motion.norm_scalar, norm_mul]

section Array
variable {V : Type} [Fintype V] [DecidableEq V]

def location (L p n : ℕ) (h : n ≤ L) (d : V → ℕ)
    (o : V → Site (C.side n p)) (t : V → Motion)
    (a : Atom C L p n h d) : Site (C.side L p) :=
  affine (t a.1).1 ((C.S.toDepth h p).embed (o a.1))
    ((C.S.toDepth h p).assemble (0, a.2.1))

def coefficients (L p n : ℕ) (h : n ≤ L) (d : V → ℕ) (t : V → Motion)
    (v : (i : V) → Palette C (d i)) (φ : V → Body)
    (a : Atom C L p n h d) : ℂ :=
  amplitude C L p (d a.1) n h (t a.1) (v a.1) (φ a.1) a.2.1 a.2.2

def kernels (L p n : ℕ) (h : n ≤ L) (d : V → ℕ)
    (o : V → Site (C.side n p)) (t : V → Motion)
    (a : Atom C L p n h d) : Config G (C.side L p) → ℂ :=
  presented (C.localSection (kept a.2.2.1)) (location C L p n h d o t a)
    (C.path.rep L p L).p.threshold (nativeLabel C (d a.1) (t a.1) a.2.2)

omit [Fintype V] [DecidableEq V] in
theorem summand (hC : C.Makes) (L p n : ℕ) (h : n ≤ L) (d : V → ℕ)
    (o : V → Site (C.side n p)) (t : V → Motion)
    (v : (i : V) → Palette C (d i)) (φ : V → Body)
    (a : Atom C L p n h d) (U : Config G (C.side L p)) :
    coefficients C L p n h d t v φ a * kernels C L p n h d o t a U =
      weights C L p n h d t v φ a * atoms C L p n h d o t a U := by
  unfold kernels
  rw [← native_atom C hC]
  simp only [Pi.smul_apply, smul_eq_mul, coefficients, ActualRG05PhysicalSource.weights,
    weight_factor, atoms, location, mul_assoc]

theorem aggregate_clinic (hC : C.Makes) (L p n : ℕ) (h : n ≤ L)
    (d : V → ℕ) (o : V → Site (C.side n p)) (t : V → Motion)
    (v : (i : V) → Palette C (d i)) (φ : V → Body) :
    JointSignedInitialization.Rooted.aggregate Sigma.fst
      (coefficients C L p n h d t v φ) (kernels C L p n h d o t) =
        fun i => clinic C p L (d i) (v i) n (o i) (t i) (φ i) := by
  rw [← aggregate_clinics C hC L p n h d o t v φ]
  funext i U
  unfold JointSignedInitialization.Rooted.aggregate
  apply Finset.sum_congr rfl
  intro a _
  split
  · exact summand C hC L p n h d o t v φ a U
  rfl

end Array
end YM.Integration.ActualRG05NativeAtoms
