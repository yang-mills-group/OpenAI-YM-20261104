import YM.MSbar.Super.Pipe

/-!
# Lifts of letters and homogeneity of terms

A lift reuses Fourier substitutions, without injectivity needed. Include widening
an alphabet and merging. And in term Rank use exact homogeneity projection, allowing all
formally nonlinear terms still with arbitrary support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β γ : Type*}
section
variable [Fintype α] {p : α→Bool}
def placeIn [DecidableEq β] (φ : α→β) : Slots α β := fun a b => if b=φ a then 1 else 0
variable [DecidableEq β]
omit [Fintype α] in
lemma avoid_place (q : β→Bool) (φ : α→β) : Slots.Avoid (q ∘ φ) q (placeIn φ) := by rintro a b; simp [placeIn]; intro e; rw [e]
lemma replay_in (φ : α→β) (h : Injective φ) (f : Term α) (L : List α) : replay (placeIn φ) f (L.map φ)=f L := by
  induction L generalizing f with
  | nil => rfl
  | cons a L ih =>
      classical
      simp_rw [List.map_cons,replay_cons,placeIn, h.eq_iff, ih]; simp
lemma replay_injective (φ : α→β) (h : Injective φ) : Injective (replay (placeIn φ)) := fun f g e => funext fun L => by rw [←replay_in φ h f L,←replay_in φ h g L,e]
@[simp] lemma replay_place [Fintype β] [DecidableEq α] (φ : α→β) (a : α) : replay (placeIn φ) (letter a)=letter (φ a) := by simp [replay_letter,placeIn, ite_smul]
@[simp] lemma replay_ditto [DecidableEq α] (f : Term α) : replay (placeIn id) f=f := funext fun _ => by simpa using replay_in id injective_id f _
variable [Fintype β]
omit [Fintype α] in
@[simp] lemma place_bridge (φ : α→β) (u : Slots β γ) : slotsBridge (placeIn φ) u=u ∘ φ := by ext a c; simp [placeIn,slotsBridge]
@[simp] lemma replay_once (φ : α→β) (u : Slots β γ) (f : Term α) : replay u (replay (placeIn φ) f)=replay (u ∘ φ) f := by rw [←replay_comp,place_bridge]
@[simp] lemma replay_twice [DecidableEq γ] (φ : α→β) (ψ : β→γ) (f : Term α) : replay (placeIn ψ) (replay (placeIn φ) f)=replay (placeIn (ψ∘φ)) f := replay_once ..
end
section
variable {f g : Term α}
/-- Only ranks with `R` predicate (on arity). -/
def Rank (R : ℕ → Prop) (f : Term α) := ∀ L, ¬R L.length → f L=0
open scoped Classical in
def ratio (R : ℕ → Prop) : Term α →ₗ[ℂ] Term α where
  toFun f L := if R L.length then f L else 0
  map_add' := by intros; funext L; split <;> simp_all
  map_smul' := by intros; funext L; split <;> simp_all
open scoped Classical in
lemma ratio_at (R : ℕ → Prop) (L : List α) (f : Term α) : ratio R f L= if R L.length then f L else 0 := rfl
abbrev exactRank (r : ℕ) := Rank (α:=α) (·=r)
abbrev chunk (r : ℕ) := ratio (α:=α) (·=r)
lemma chunk_at (r : ℕ) (L : List α) (f : Term α) : chunk r f L= if L.length=r then f L else 0 := by rw [chunk,ratio_at]; split <;> simp_all
variable {R S : ℕ → Prop} {p : α→Bool} {r : Bool}
lemma Rank.cut_iff : Rank R f ↔ ratio R f=f := by
  constructor
  · intro h; funext L; rw [ratio_at]; split <;> simp_all [Rank]
  intro h L H; rw [← h,ratio_at,if_neg H]
lemma Rank.mono (h : Rank R f) (H : ∀ r,R r→S r) : Rank S f := fun a t => h a (fun u => t (H _ u))
lemma Rank.smul (h : Rank R f) (c : ℂ) : Rank R (c • f) := cut_iff.mpr (by simp only [map_smul,cut_iff.mp h])
lemma Rank.add (h : Rank R f) (H : Rank R g) : Rank R (f+g) := cut_iff.mpr (by rw [map_add,cut_iff.mp h,cut_iff.mp H])
lemma Rank.zero (R) : Rank R (0 : Term α) := cut_iff.mpr (map_zero _)
lemma Rank.sub (h : Rank R f) (H : Rank R g) : Rank R (f-g) := cut_iff.mpr (by rw [map_sub,cut_iff.mp h,cut_iff.mp H])
lemma Rank.neg (h : Rank R f) : Rank R (-f) := cut_iff.mpr (by rw [map_neg,cut_iff.mp h])
lemma Rank.sum {u : Finset β} {f : β→Term α} (H : ∀ i∈u,Rank R (f i)) : Rank R (∑ i∈u,f i) := cut_iff.mpr ((map_sum (ratio R) ..).trans (sum_congr rfl fun i e => cut_iff.mp (H i e)))
lemma rank_ratio (f : Term α) (R) : Rank R (ratio R f) := fun L H => by rw [ratio_at,if_neg H]
lemma Rank.peel (h : Rank R f) (x : α) : Rank (fun t => R (t+1)) (peel x f) := fun _ e => h _ e
lemma peel_ratio (x : α) (f : Term α) (R) : peel x (ratio R f)=ratio (fun t => R (t+1)) (peel x f) := by funext i; simp_rw [peel_apply,ratio_at,peel_apply,List.length_cons] -- maybe simp fails
lemma Grade.ratio (h : Grade p r f) (R) : Grade p r (ratio R f) := fun L H => by simp [ratio_at,h L H]
lemma Ordered.ratio (h : Ordered p f) (R) : Ordered p (ratio R f) := by intro A x y L; simp only [ratio_at,List.length_append,List.length_cons]; split <;> simp_all [h A x y L]
lemma Scalar_rank (c : ℂ) : exactRank (α:=α) 0 (scalar c) := fun L H => by cases L; simp at H; rfl
lemma Letter_rank [DecidableEq α] (a : α) : exactRank 1 (letter a) := by intro L H; rcases L with _|⟨x,_|⟨y,z⟩⟩ <;> simp_all [letter,scalar]

lemma replay_ratio [Fintype α] (u : Slots α β) (f : Term α) (R : ℕ → Prop) : replay u (ratio R f)=ratio R (replay u f) := by
  funext L; induction L generalizing f R with
  | nil => simp only [replay_nil,ratio_at,replay_nil,List.length_nil]
  | cons a L ih =>
    simp only [replay_cons,peel_ratio,ratio_at,List.length_cons]; by_cases h : R (L.length+1) <;> simp_all [ratio_at]
lemma rank_replay [Fintype α] (h : Rank R f) (u : Slots α β) : Rank R (replay u f) := Rank.cut_iff.mpr (by rw [← replay_ratio,Rank.cut_iff.mp h])
end
end YM.MSBar.Super
