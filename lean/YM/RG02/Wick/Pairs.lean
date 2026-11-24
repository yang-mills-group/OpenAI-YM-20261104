import YM.Next.RANK.GaussTrack
import YM.RG02.Marker.Remove
import YM.RG02.Marker.Partition
import YM.RG02.Marker.Product

/-!
Pairings with names in a square-free census of leg **occurrences**.
Carries the identity of every line through partition/log; not pictured
lines modulo equivalence. There is no diagonal admissibility assumption
on the covariance (self-contractions at a vertex/repeated positions read
it with multiple occurrence names). `blend` already does this irrespective
of names, by recursion; here is the mode expansion needed for passing it
through joint cumulants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick
open Filter Marker Multi Finset Extra.Trajectories Marks Remove Next.Rank Next.Rank.Normal
open scoped BigOperators Classical
variable {A W : Type} [DecidableEq A] [Fintype A]

def given (p : Finset A) : (full A).Mode := ⟨p,mem_univ _⟩

/-- Unordered pairing value on legs; division by two here only to free
orientation. -/
def two (q : Symmetric W) (v : A → W) (s : (full A).Mode) : ℂ :=
  if s.val.card=2 then (∑ i∈s.val, ∑ j∈s.val.erase i, q.cov (v i) (v j))/2 else 0

def origin (q : Symmetric W) (v : A → W) := Poly.inject fun s => two q v s

lemma two_pair (q : Symmetric W) (v : A → W) (i j : A) (hi : i ≠ j) :
    two q v (given {i,j})=q.cov (v i) (v j) := by
  dsimp only [two,given]; rw [if_pos (card_pair hi),sum_insert (by simpa using hi), erase_insert (by simpa using hi)]
  simp only [sum_singleton]
  rw [Finset.pair_comm i j, erase_insert (by simpa using Ne.symm hi),sum_singleton, q.symm (v j)]
  ring

lemma origin_quiet (q : Symmetric W) (v : A → W) : (origin q v).part (full A).quiet=0 := by
  simp [origin,two,Poly.part,Poly.inject,Census.quiet]

-- differential recursion on the squares in the full census
private lemma twoD (q : Symmetric W) (v : A → W) (i : A) :
    euler i (origin q v) = factor (full A) i * Multi.lambda (full A) (fun j => q.cov (v i) (v j)) := by
  ext t
  rw [part_euler,restores]
  split; rename_i hi
  · change (if t.val.card=2 then _ else _)=_
    split; rename_i he
    · have hh : (shave t i).val.card=1 := by change (t.val.erase i).card=1; rw [card_erase_of_mem hi,he]
      obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hh
      change t.val.erase i={j} at hj
      have hn : i ≠ j := by intro h; exact notMem_erase i t.val (by rw [hj]; simpa using h)
      have hq : t = given {i,j} := Subtype.ext (show t.val = {i,j} by nth_rw 1 [← insert_erase hi]; rw [hj])
      rw [show shave t i=(full A).fire j from Subtype.ext hj, lambda_part]
      have hb := two_pair q v i j hn; rw [←hq,two,if_pos he] at hb; exact hb
    rename_i he
    have hz (j : A) : shave t i ≠ (full A).fire j := fun H => he (by
      have hb : t.val.erase i={j} := congr_arg Subtype.val H
      have ha := congr_arg Finset.card hb; rw [card_singleton,card_erase_of_mem hi] at ha; omega)
    symm; rw [lambda,Poly.part_sum]; apply sum_eq_zero; intro j _; rw [Poly.part_send,if_neg (hz j)]
  rfl

private lemma peels (p : Poly (full A))(i : A)(s : Finset A)(hi : i ∉ s)(v : A → ℂ) :
    (factor (full A) i * Multi.lambda (full A) v * p).part (given (insert i s)) =
       ∑ j∈s,v j * p.part (given (s.erase j)) := by
  let R := full A
  rw [mul_assoc, restores, if_pos (show i∈(given (insert i s)).val from mem_insert_self ..)]
  rw [show shave (given (insert i s)) i = given s from Subtype.ext (erase_insert hi), Multi.lambda,sum_mul,Poly.part_sum]
  trans ∑ j∈s,(Poly.send (R.fire j) (v j) * p).part (given s)
  · symm; apply sum_subset (subset_univ _); intro j _ hj
    rw [Primitives.GCC.Anchor.mul_at_part]
    exact if_neg (fun h => hj (h (mem_singleton_self j)))
  apply sum_congr rfl; intro j hj
  rw [Primitives.GCC.Anchor.mul_at_part, if_pos (show (R.fire j).val ⊆ (given s).val from (singleton_subset_iff.mpr hj : ({j}:Finset A) ⊆ s))]
  rw [show Primitives.GCC.Anchor.diff (given s) (R.fire j).val = given (s.erase j) from Subtype.ext (sdiff_singleton_eq_erase ..)]

theorem docket (q : Symmetric W)(v : A → W)(s : Finset A) :
    blend q 0 (Normal.glyphs v s)=(Poly.pass (origin q v)).part (given s) := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    obtain rfl|⟨i,hi⟩ := s.eq_empty_or_nonempty
    · rw [glyphs,prod_empty, Normal.fresh]; exact (Poly.pass_part _ (origin_quiet q v)).symm
    let p := s.erase i
    have hp : s=insert i p := (insert_erase hi).symm
    rw [← if_pos (α:=ℂ) (t:=(Poly.pass (origin q v)).part (given s)) (e:=0) (show i∈(given s).val from hi), ← part_euler, euler_pass (origin_quiet ..)]
    rw [twoD,hp,mul_comm (Poly.pass (origin q v)),peels _ _ p (notMem_erase i s),spring 0 q v p (notMem_erase i s)]
    simp only [Pi.zero_apply,zero_mul,zero_add]
    exact sum_congr rfl fun i _ => congr_arg (fun c => _ * c) (ih (p.erase i) (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) (erase_ssubset hi)))

abbrev Lines (A : Type) [DecidableEq A] [Fintype A] := Multi.parts (Marks.full A)

def CompleteOn (s : Finset A)(p : (Lines A).Mode) := (Multi.unionOf p).val=s ∧ ∀ i∈p.val, i.val.val.card=2
instance (s : Finset A)(p : (Lines A).Mode) : Decidable (CompleteOn s p) := by unfold CompleteOn; infer_instance

/-- All pairings once each. `joint_assembly` will retain them across
stochastic tags in a moment extraction. -/
theorem pairing (q : Symmetric W)(v : A → W)(s : Finset A) :
    blend q 0 (glyphs v s) = ∑ p : (Lines A).Mode,
       if CompleteOn s p then ∏ i∈p.val, two q v i.val else 0 := by
  rw [docket, pass_partition (origin_quiet ..),shards, Finset.sum_filter]; apply sum_congr rfl; intro i _
  by_cases h : CompleteOn s i
  · rw [if_pos h, if_pos (Subtype.ext h.1)]; rfl
  rw [if_neg h]; split; rename_i hh
  · have hu : ¬∀ k∈i.val,k.val.val.card=2 := fun HK => h ⟨congr_arg Subtype.val hh,HK⟩
    push Not at hu; obtain ⟨j,hj,hf⟩ := hu
    exact prod_eq_zero hj (if_neg hf : two q v j.val=0)
  rfl

end YM.RG02.Wick
