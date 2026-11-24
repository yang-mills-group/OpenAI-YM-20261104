import YM.Integration.WilsonCenteredCaptureCensus
import YM.Push.LOCAL_SPLITTING.Recovery

/-! A field-independent filing of all absorbed original owners in actual
dormant slots. The marked payload sits inside its original eligible
family, and retains each old quiet factor's own predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureSlots
open Finset Function Lattice RG Wilson Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} (P : Rep G n) (K : Guard.Keeper P.p P.activities)
    (T : ι → Support n) (I : ι → Finset ℕ) (serial : ι × Finset ℕ ↪ ℕ)

structure Shape (i : ι) (C : Finset ℕ) : Prop where
  live : C.Nonempty
  kept : I i ⊆ C
  hits : ∀ j ∈ C, j ∈ I i ∨ ¬Disjoint (T i) (P.activities.forced j).support
  apart : (C : Set ℕ).Pairwise (fun i j=>Disjoint (P.activities.forced i).support (P.activities.forced j).support)

abbrev Key := {q : ι × Finset ℕ // Shape P T I q.1 q.2}

def slot : Key P T I ↪ ℕ where
  toFun q := K.code (docket P (T q.val.1) q.val.2 q.property.live (serial q.val))
  inj' _ _ eq := Subtype.ext (serial.injective (congrArg Prod.snd (K.code.injective eq)))

theorem support (q : Key P T I) :
    (P.activities.forced (slot P K T I serial q)).support = ground P (T q.val.1) q.val.2 :=
  K.support _

def payload (f : ι → Config G n → ℂ) (q : Key P T I) (U : Config G n) : ℂ :=
  if (P.activities.forced (slot P K T I serial q)).eligible P.p.threshold U then
    f q.val.1 U * ∏ j ∈ q.val.2 \ I q.val.1, (P.activities.K j U : ℂ) else 0

def entered (f : ι → Config G n → ℂ) : ℕ → Config G n → ℂ :=
  Function.extend (slot P K T I serial) (payload P K T I serial f) 0

theorem registered (f : ι → Config G n → ℂ) (q : Key P T I) :
    entered P K T I serial f (slot P K T I serial q) = payload P K T I serial f q :=
  (slot P K T I serial).injective.extend_apply ..

theorem outside (f : ι → Config G n → ℂ) (j : ℕ) (unused : ¬∃ q, slot P K T I serial q = j) :
    entered P K T I serial f j = 0 := Function.extend_apply' _ _ _ unused

/-- The actual forced array produced by the filing satisfies the original
strong locality and inventory format, including on rough configurations. -/
theorem formed (f : ι → Config G n → ℂ) (o : Site n)
    (law : P.activities.ForcedFamily P.p) (anchor : ∀ z, o ∈ T z)
    (locality : ∀ z, Attaches P.p.threshold (T z) (f z)) :
    ForceFormat P.p P.activities o (entered P K T I serial f) := by
  refine ⟨fun j U neq=>?_,fun j neq=>?_,fun j=>?_,fun j=>?_,fun j=>?_⟩
  all_goals by_cases used : ∃ q, slot P K T I serial q = j
  all_goals first | obtain ⟨q,rfl⟩ := used | simp only [outside P K T I serial f j used] at *
  · rw [registered,payload] at neq
    split at neq
    · assumption
    exact (neq rfl).elim
  · exact (neq rfl).elim
  · rw [show Push.Local.patch P.activities (slot P K T I serial q) = ground P (T q.val.1) q.val.2 from support ..]
    exact mem_union_left _ (anchor q.val.1)
  · exact (neq rfl).elim
  · intro gauge U
    rw [registered,payload,payload]
    simp only [Work.H03.eligible_gauge _ _ _ _ (law.symtest _ gauge U),(locality q.val.1).symmetry gauge U,fun j=>law.sym j gauge U]
  · intro _ _
    rfl
  · rw [registered]
    intro U V huv hflags
    unfold payload
    rw [Work.H03.eligible_reads _ _ (law.reads_test _) U V huv hflags]
    rw [show Push.Local.patch P.activities (slot P K T I serial q) = ground P (T q.val.1) q.val.2 from support ..] at huv hflags
    split
    · rw [Work.H03.reads_larger (Finset.subset_union_left (s₂:=q.val.2.biUnion (Push.Local.patch P.activities))) (locality q.val.1).sites U V huv hflags]
      congr 1
      exact Finset.prod_congr rfl (fun j hj => congrArg Complex.ofReal (Work.H03.reads_larger
        ((Finset.subset_biUnion_of_mem _ (mem_sdiff.mp hj).1).trans Finset.subset_union_right)
        (law.reads j) U V huv hflags))
    rfl
  · intro _ _ _ _
    rfl
  · rw [registered]
    unfold payload
    exact Measurable.ite (Work.H03.eligible_measurable _ _ (law.meas_test _)) ((locality _).borel.mul
      (Finset.measurable_fun_prod _ fun j _ => Complex.continuous_ofReal.measurable.comp (law.meas j))) measurable_const
  · exact measurable_const

end YM.Integration.WilsonCenteredCaptureSlots
