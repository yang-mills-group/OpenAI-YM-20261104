import YM.Integration.ActualStencilPortraits
import YM.RemainderComparison.Encore.Voice

/-! The existing marked-density compiler on an already chosen representation.
The proof adapts the public Rider.Markov product expansion, without creating
a Placement.file representation. Distinct registered log slots are structural
receipts; no normalized comparison estimate is assumed or asserted here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Function Lattice RG Wilson Finset MeasureTheory
open Push Push.AbsoluteSums PhysicalNext.Repeat
open Push.AbsoluteSums.Animals
open RemainderComparison RemainderComparison.Typeface
open RemainderComparison.Encore RemainderComparison.Mosaic
open RemainderComparison.Serif RemainderComparison.Muse
open RemainderComparison.Lyric
open Lotus
open Merge Palette Marker
open scoped BigOperators Classical

variable {G : Gauge} {f c : Side} (R : Rep G f) (S : StepData c f)
    {ι : Type} [Fintype ι] {α : Type*}
    (M : ι → Portrait R α) (tests : α) (slot : ι → ℕ)
    (hslot : Injective slot) (hwing : ∀ i, (M i).wing = Wing.logKey (slot i))
    {V : Type} [DecidableEq V] (B : Marker.Census V) (z : ι → Marker.Poly B)

include hslot hwing

/-- Exact unnormalized marked density, uniformly as an identity for every
test choice and field, on this same `R`. The tag product keeps collisions. -/
theorem log_portrait_marked_density (U : Config G f) :
    Serif.TuneR (brand M tests) Set.univ (fun _ => 1) 0 z S U =
      ((R.eval U : ℝ) : ℂ) •
        ∏ i, (1 + (((M i).angle tests).ingredient U : ℂ) • z i) := by
  let A := brand M tests
  have hw : Injective (fun i => (M i).wing) := by
    intro i j hij
    change (M i).wing = (M j).wing at hij
    rw [hwing i, hwing j] at hij
    exact hslot (Wing.logKey.inj hij)
  let q : Drums A S → Finset ι := Subtype.val
  have hsign : Injective (fun i => Palette.sign A S i) := (Team.badged S).comp hw
  have hq : Surjective q := fun s => ⟨⟨s, hsign.injOn⟩, rfl⟩
  let eqv := Equiv.ofBijective q ⟨Subtype.val_injective, hq⟩
  have hval (s : Finset ι) : (eqv.symm s).val = s := eqv.apply_symm_apply s
  let C (i : ι) : Marker.Poly B := (((M i).angle tests).ingredient U : ℂ) • z i
  have hC (i : ι) :
      Encore.primitive A U Set.univ (Muse.sits Set.univ (fun _ => 1) 0) z i = C i := by
    unfold Encore.primitive C A
    rw [Typeface.photo]
    simp [Verse.controls, Muse.sits, Verse.marked]
  have hbase (s : Drums A S) :
      (team A s).cicada U = R.eval U * (team A s).ingredients U := by
    let T := team A s
    have hgas : T.gasDue = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨v, hv, hp⟩ := (Team.asked T i).mp hi
      obtain ⟨j, _, rfl⟩ := mem_image.mp hv
      change (M j).wing = Wing.gasKey i at hp
      rw [hwing j] at hp
      cases hp
    have hb (i : Finset ℕ) : T.bun i U =
        R.activities.gasOccurrence R.p i U * T.ingredients U := by
      unfold Team.bun Activities.gasOccurrence Team.bill
      rw [hgas, if_pos (empty_subset _), sdiff_empty]
      split
      · apply mul_comm
      · simp
    change Real.exp _ * (∑' i, T.bun i U) = _
    simp_rw [hb]
    rw [tsum_mul_right, ← mul_assoc]
    rfl
  have hterm (s : Drums A S) :
      (Mosaic.raw A s).paint Set.univ (Muse.sits Set.univ (fun _ => 1) 0) z U =
        ((R.eval U : ℝ) : ℂ) • ∏ i ∈ s.val, C i := by
    unfold Verse.paint Verse.emit
    simp_rw [← hC]
    rw [Encore.labeled]
    rw [smul_smul, ← Complex.ofReal_mul]
    apply congr_arg (fun r : ℝ => (r : ℂ) • _)
    change _ * (team A s).cicada U = _
    rw [hbase]
    exact mul_left_comm ..
  change Serif.TuneR A Set.univ (fun _ => 1) 0 z S U = _
  unfold Serif.TuneR
  rw [tsum_fintype, Finset.prod_one_add]
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  apply congr_arg ((R.eval U : ℂ) • ·)
  rw [Finset.powerset_univ]
  rw [← Equiv.sum_comp eqv.symm (fun s : Drums A S => ∏ i ∈ s.val, C i)]
  simp_rw [hval]
  rfl

omit hslot hwing

/-- Apply the product identity to the literal masked stencils, with each
slot's test chosen independently. Registration refers to this exact `R`.
The original computed prices are retained alongside the density identity. -/
theorem registered_marked_density
    {E : ι → Type*} {orders radii : ι → ℕ} {costs : ι → ℝ}
    (D : ∀ i, Placement.Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site f) (slots : ι → ℕ)
    (hslots : Injective slots) (hβ : 0 < R.beta)
    (hreg : ∀ i, R.activities.reg (slots i) = Placement.Tile.aperture (positions i) (radii i))
    (hzero : ∀ i, R.activities.E (slots i) = 0) :
    ∃ M : ∀ i, Portrait R (E i),
      (∀ i, (M i).wing = Wing.logKey (slots i)) ∧
      (∀ i, (M i).weight = Placement.Tile.peso G (orders i) (radii i) (costs i) R.p) ∧
      ∀ (tests : ∀ i, E i) (U : Config G f),
        Serif.TuneR (brand (independentPortraits M) tests) Set.univ (fun _ => 1) 0 z S U =
          (R.eval U : ℂ) • ∏ i, (1 +
            ((masked R.p.threshold (neighbors (radii i) (positions i))
              (Placement.Tile.read (D i) (positions i) (tests i)) U : ℝ) : ℂ) • z i) := by
  obtain ⟨M, hwing, hweight, hread⟩ :=
    registered_independent_portraits R D base positions slots hβ hreg hzero
  refine ⟨M, hwing, hweight, ?_⟩
  intro tests U
  rw [log_portrait_marked_density R S (independentPortraits M) tests slots hslots hwing B z U]
  apply congr_arg ((R.eval U : ℂ) • ·)
  apply Finset.prod_congr rfl
  intro i _
  rw [hread tests i]

end YM.Integration
