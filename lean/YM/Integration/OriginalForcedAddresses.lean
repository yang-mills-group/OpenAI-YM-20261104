import YM.MergeProof.Grant
import YM.FullVolume.Cross

/-!
Exact rebooking of finite barcode coefficients in the existing activity
dictionary. The routing is fixed before the coefficient family is supplied.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OriginalForcedAddresses
open Finset Function Set MeasureTheory Lattice Wilson RG
open MergeProof MergeProof.Accent Marker Extra.Histories Planned.GuardedAtom
open PhysicalNext.Repeat.Legato
open scoped BigOperators

variable {G : Gauge} {n : Side} {P : Rep G n} {Y : Type*}

def rebook (K : Guard.Keeper P.p P.activities) (f : Box n → Y → ℂ) :
    ℕ → Y → ℂ :=
  extend (cart K) (f ∘ Subtype.val) 0

theorem at_address (K : Guard.Keeper P.p P.activities) (f : Box n → Y → ℂ)
    (s : StockTag n) : rebook K f (cart K s) = f s.val :=
  (cart K).injective.extend_apply ..

theorem off_address (K : Guard.Keeper P.p P.activities) (f : Box n → Y → ℂ)
    {i : ℕ} (hi : i ∉ Set.range (cart K)) : rebook K f i = 0 :=
  extend_apply' _ _ _ hi

theorem same_barcode (K : Guard.Keeper P.p P.activities) (s : StockTag n) :
    barcode P.activities (cart K s) = s.val := cardK K s

theorem aggregate (K : Guard.Keeper P.p P.activities) (f : Box n → Y → ℂ)
    (hf : ∀ s, ¬ Sure s → f s = 0) (y : Y) :
    cram (barcode P.activities) (fun i => rebook K f i y) = fun s => f s y := by
  classical
  funext s
  rw [expand_eq]
  by_cases hs : Sure s
  · let tag : StockTag n := ⟨s, hs⟩
    rw [tsum_eq_single (cart K tag)]
    · rw [if_pos (cardK K tag), at_address]
    intro i hi
    split_ifs with hb
    · apply congrFun (off_address K f ?_) y
      rintro ⟨other, rfl⟩
      exact hi (congrArg (cart K) (Subtype.ext ((cardK K other).symm.trans hb)))
    · rfl
  · rw [congrFun (hf s hs) y]
    refine (tsum_congr ?_).trans tsum_zero
    intro i
    split_ifs with hb
    · apply congrFun (off_address K f ?_) y
      rintro ⟨tag, rfl⟩
      exact hs (((cardK K tag).symm.trans hb) ▸ tag.property)
    · rfl

theorem summable (K : Guard.Keeper P.p P.activities) (f : Box n → Y → ℂ)
    (y : Y) : Summable (fun i => rebook K f i y) := by
  classical
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range (cart K)).subset
  intro i hi
  by_contra hn
  exact hi (congrFun (off_address K f hn) y)

theorem profile_eq (K : Guard.Keeper P.p P.activities)
    (f : Box n → Config G n → ℂ) (hf : ∀ s, ¬ Sure s → f s = 0) :
    profile P.activities (rebook K f) = f := by
  funext s U
  exact congrFun (aggregate K f hf U) s

variable {V : Type*} [DecidableEq V] {B : Census V}

theorem coefficient_zero (o : V → Site n) (F : Box n → Config G n → Poly B)
    (hF : ∀ s, Flow o s (F s) P.p.threshold) (i : B.Mode)
    (s : Box n) (hs : ¬ Sure s) : (fun U => (F s U).part i) = 0 := by
  funext U
  have hz : F s U = 0 := by
    by_contra hn
    exact hs ((hF s).permits U hn).2
  rw [hz]
  rfl

theorem singleton_profile (K : Guard.Keeper P.p P.activities)
    (o : V → Site n) (F : Box n → Config G n → Poly B)
    (hF : ∀ s, Flow o s (F s) P.p.threshold) (v : V) :
    profile P.activities (rebook K (fun s U => (F s U).part (B.fire v))) =
      fun s U => (F s U).part (B.fire v) :=
  profile_eq K _ (coefficient_zero o F hF (B.fire v))

theorem singleton_gas (K : Guard.Keeper P.p P.activities)
    (o : V → Site n) (F : Box n → Config G n → Poly B)
    (hF : ∀ s, Flow o s (F s) P.p.threshold)
    (hquiet : ∀ s U, (F s U).part B.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) s U)
    {e t : ℝ} (hP : P.activities.Valid P.p e t) (v : V) (U : Config G n) :
    (Accent.field (fun s => F s U) (flags P.p.threshold U)).part (B.fire v) =
      ∑' b, Accent.nickel P.p P.activities b U
        (fun i => rebook K (fun s W => (F s W).part (B.fire v)) i U) := by
  apply Accent.stageR P.activities P.p U (Accent.mass_crest P.activities hP U)
    (fun s => hquiet s U) (summable K _ U)
  intro s
  exact (congrFun (congrFun (singleton_profile K o F hF v) s) U).symm

def actual_keeper (R : Run G) (hG : G.Simple) (N m p : ℕ) (hm : m ≤ N) :
    Guard.Keeper (R.family.path.rep N p m).p
      (R.family.path.rep N p m).activities :=
  Guard.Keeper.sufficient (R.tuning.receipts.samples hG N m p hm)

theorem actual_address_blank (R : Run G) (hG : G.Simple)
    (N m p : ℕ) (hm : m ≤ N) (s : StockTag (R.family.S.side m p)) :
    (R.family.path.rep N p m).activities.K
      (cart (actual_keeper R hG N m p hm) s) = 0 := by
  exact Guard.Keeper.blank (R.tuning.receipts.samples hG N m p hm) (s, 0)

end YM.Integration.OriginalForcedAddresses
