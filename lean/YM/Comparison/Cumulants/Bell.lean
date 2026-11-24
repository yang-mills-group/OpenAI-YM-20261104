import YM.Next.MULTISOURCE.First
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra

/-!
# Order and marker convention I: connected versus ordinary

We use the *same* polynomial algebra as `YM.Marker.Poly`, including the allowed-set
truncation. Bell partitions are `Multi.shards`: unordered sets of nonempty disjoint
blocks, each a set of DISTINCT NAMES, with prescribed union. Nothing refers to the
physical *values* of the vertices named by those names.

In particular this counts coincident or identical inputs with distinct names correctly.
For stochastic shared tags average joint moments before using any such log. See
`total_cumulance`: there's still an *outer* connected operation on the tag law after
forming conditional cumulants. Divisions of possibly unnormalized inputs to this
calculation, with the correct vacuum scalar factors, will be separate operations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Cumulants

open Finset Function Marker Multi Extra.Trajectories Primitives.GCC
open scoped BigOperators

variable {V V' : Type} [DecidableEq V] [DecidableEq V'] {R : Census V}
  {R' : Census V'}

lemma eq_quiet_of_empty (s : R.Mode) (h : ¬ s.val.Nonempty) : s = R.quiet :=
  Subtype.ext (not_nonempty_iff_eq_empty.mp h)

lemma lit_expansion (a : Poly R) (h : a.part R.quiet = 0) :
    lit R (fun x => a.part x.val) = a := by
  ext s
  by_cases hs : s.val.Nonempty
  · exact part_lit _ ⟨s,hs⟩
  rw [eq_quiet_of_empty s hs, h, part_lit_quiet]

lemma substitute_quiet (a : Poly (parts R)) :
    (substitute R a).part R.quiet = a.part (parts R).quiet := by
  classical
  rw [substituted a, sum_eq_single (parts R).quiet]
  · intro b hb ht
    exfalso
    have he := (Finset.mem_filter.mp hb).2
    have hh : b.val.Nonempty := fun_nonempty b ht
    have hr := (unionOfHot (⟨b,hh⟩ : Multi.Hot (parts R))).property
    change (unionOf b).val.Nonempty at hr
    rw [he] at hr
    simp [Census.quiet] at hr
  · simp [shards]
where
  fun_nonempty (b : (parts R).Mode) (ht : b ≠ (parts R).quiet) : b.val.Nonempty := by
    by_contra! h
    apply ht
    exact Subtype.ext h

variable [Fintype V] [Fintype V']

lemma connected_of_pass {a : Poly R} (ha : a.part R.quiet = 0) :
    connected a.pass = a := by
  have h := a.pass_part ha
  exact pass_inj (connected_quiet h) ha (pass_connected h)

lemma connected_unit : connected (1 : Poly R) = 0 :=
  show _ from by
    rw [← pass_zero (R:=R), connected_of_pass (Poly.part_nil _)]

lemma connected_product {a b : Poly R} (ha : a.part R.quiet = 1) (hb : b.part R.quiet = 1) :
    connected (a*b) = connected a + connected b := by
  have h₁ := connected_quiet ha
  have h₂ := connected_quiet hb
  have ht : (connected a+connected b).part R.quiet=0 := by rw [Poly.part_plus,h₁,h₂,add_zero]
  conv_lhs => rw [← pass_connected ha, ← pass_connected hb, ← pass_add h₁ h₂]
  exact connected_of_pass ht

lemma connected_map (f : Poly R →ₐ[ℂ] Poly R')
    (h : ∀ x, (f x).part R'.quiet = x.part R.quiet) {x : Poly R} (hx : x.part R.quiet = 1) :
    connected (f x) = f (connected x) := by
  have he := connected_quiet hx
  have hq : (f (connected x)).part R'.quiet = 0 := Eq.trans (h _) he
  conv_lhs => rw [← pass_connected hx, pass_map f (connected x) he hq]
  exact connected_of_pass hq

lemma connected_dilation (v : V → ℂ) {x : Poly R} (h : x.part R.quiet = 1) :
    connected (dilation R v x) = dilation R v (connected x) :=
  connected_map _ (fun _ => by simp [dilation_part,Census.quiet]) h

/-- Bell partitions. Exponential generating function in this convention has the usual
`1/i!` on powers (`Poly.pass`), but *no extra factorial anywhere in this formula*. -/
lemma pass_bell {a : Poly R} (h : a.part R.quiet = 0) (s : R.Mode) :
    a.pass.part s = ∑ q∈shards R s, ∏ b∈q.val, a.part b.val := by
  let f : Multi.Hot R → ℂ := fun i => a.part i.val
  have he : substitute R (lambda (parts R) f) = a :=
    (substitute_lambda f).trans (lit_expansion a h)
  rw [show a.pass = substitute R (Poly.pass (lambda (parts R) f)) by
    rw [pass_map _ _ (lambda_quiet _) (by rw [he,h]), he]]
  rw [substituted]
  exact sum_congr rfl fun i _ => pass_fire f i

lemma bell_moment {x : Poly R} (h : x.part R.quiet = 1) (t : R.Mode) :
    x.part t = ∑ q∈shards R t, ∏ b∈q.val, (connected x).part b.val := by
  nth_rw 1 [← pass_connected h]
  exact pass_bell (connected_quiet h) _

/-! ### Law of total cumulance, in the same algebra -/

section Mixing
variable {Θ : Type*}

/-- This permits complex weights. The expectation/vacuum accounting supplying those
weights needs its own proof. -/
def mix (u : Finset Θ) (w : Θ → ℂ) (M : Θ → Poly R) :=
    ∑ i∈u,w i • M i

omit [Fintype V] in
lemma mix_part (u : Finset Θ) (w : Θ → ℂ) (M : Θ → Poly R) (s) :
    (mix u w M).part s = ∑ i∈u,w i * (M i).part s := by
  simp only [mix, Poly.part_sum, Poly.part_smul]

variable {u : Finset Θ} {w : Θ → ℂ} {M : Θ → Poly R}

omit [Fintype V] in
lemma mix_normalized (hw : ∑ i∈u, w i = 1) (hm : ∀ i∈u,(M i).part R.quiet=1) :
    (mix u w M).part R.quiet = 1 := by
  rw [mix_part]
  refine (sum_congr rfl (fun i hi => show w i * _ = w i by rw [hm i hi,mul_one])).trans hw

def conditionalBlocks (u : Finset Θ) (w : Θ → ℂ) (M : Θ → Poly R) : Poly (parts R) :=
    mix u w (fun i => (lambda (parts R) (fun l : Multi.Hot R => (connected (M i)).part l.val)).pass)

/-- The joint moments being used over the outer parameter. In particular when multiple
vertices use the SAME variable of θ, this reads *their full product on that θ*. -/
lemma conditional_blocks_part (q : (parts R).Mode) :
    (conditionalBlocks u w M).part q = ∑ i∈u, w i * ∏ b∈q.val, (connected (M i)).part b.val := by
  unfold conditionalBlocks
  rw [mix_part]
  exact sum_congr rfl fun i _ => congrArg (w i * ·) (pass_fire _ q)

theorem total_cumulance (hw : ∑ i∈u,w i=1) (hm : ∀ i∈u,(M i).part R.quiet=1) :
    connected (mix u w M) = substitute R (connected (conditionalBlocks u w M)) := by
  apply Eq.trans _ (connected_map (substitute R) substitute_quiet (x:=conditionalBlocks u w M)
    (mix_normalized hw (fun i _ => Poly.pass_part _ (lambda_quiet _))))
  congr 1
  unfold conditionalBlocks mix
  rw [map_sum]
  refine sum_congr rfl fun i hi => ?_
  have hq := hm i hi
  let b := fun l : Multi.Hot R => (connected (M i)).part l.val
  have he : substitute R (lambda (parts R) b) = connected (M i) :=
    (substitute_lambda b).trans (lit_expansion _ (connected_quiet hq))
  rw [map_smul,pass_map _ _ (lambda_quiet _)
    (show (substitute R (lambda (parts R) b)).part R.quiet=0 by rw [he,connected_quiet hq])]
  change _ = _ • ((substitute R (lambda (parts R) b)).pass)
  rw [he,pass_connected hq]

/-- No arity hypotheses, no factorization of overlapping tags. -/
lemma total_cumulance_part (hw : ∑ i∈u,w i=1) (hm : ∀ i∈u,(M i).part R.quiet=1)
    (t : R.Mode) :
    (connected (mix u w M)).part t =
      ∑ q∈shards R t,(connected (conditionalBlocks u w M)).part q := by
  rw [total_cumulance hw hm,substituted]
end Mixing

/-! ### Disconnected moment data give zero mixed cumulant -/

def modeLeft (i : R.Mode) (a : Finset V) : R.Mode :=
  ⟨i.val∩a,R.down i.property _ inter_subset_left⟩
def modeRight (i : R.Mode) (a : Finset V) : R.Mode :=
  ⟨i.val\a,R.down i.property _ sdiff_subset⟩

private def leftWeight (a : Finset V) (i) := if i∈a then (1:ℂ) else 0
private def rightWeight (a : Finset V) (i) := if i∈a then (0:ℂ) else 1

omit [Fintype V] in
private lemma left_project (B : Poly R) (a : Finset V) (i : R.Mode) :
    (dilation R (leftWeight a) B).part i = if i.val⊆a then B.part i else 0 := by
  rw [dilation_part]; split
  next h => rw [prod_eq_one (by intro j hj; exact if_pos (h hj)), one_mul]
  next h =>
    obtain ⟨x,hx,hv⟩ := not_subset.mp h
    rw [prod_eq_zero hx (if_neg hv),zero_mul]

omit [Fintype V] in
private lemma right_project (B : Poly R) (a : Finset V) (i : R.Mode) :
    (dilation R (rightWeight a) B).part i = if Disjoint i.val a then B.part i else 0 := by
  rw [dilation_part]; split
  next h => rw [prod_eq_one (by intro j hj; exact if_neg (disjoint_left.mp h hj)), one_mul]
  next h =>
    obtain ⟨x,hx,hv⟩ := not_disjoint_iff.mp h
    rw [prod_eq_zero hx (show rightWeight a x = 0 from if_pos hv),zero_mul]

omit [Fintype V] in
private lemma join_disconnected (a : Finset V) (i : R.Mode) :
    Poly.merges (modeLeft i a) (modeRight i a) i := by
  change Disjoint (i.val∩a) (i.val\a) ∧ (i.val∩a) ∪ (i.val\a)=i.val
  constructor
  · exact disjoint_left.mpr fun x hx he => (mem_sdiff.mp he).2 ((mem_inter.mp hx).2)
  ext x
  by_cases hx : x∈a <;> simp [hx]

omit [Fintype V] in
private lemma join_unique (a : Finset V) {i x y : R.Mode} (h : Poly.merges x y i)
    (hx : x.val ⊆ a) (hy : Disjoint y.val a) : x=modeLeft i a ∧ y=modeRight i a := by
  have he := h.2
  refine ⟨Subtype.ext ?_,Subtype.ext ?_⟩
  · change x.val=i.val∩a
    ext u
    rw [← he,mem_inter,mem_union]
    exact ⟨fun hp => ⟨Or.inl hp,hx hp⟩,
      fun h => h.1.resolve_right (fun hr => (disjoint_left.mp hy hr) h.2)⟩
  change y.val=i.val \ a
  ext u
  rw [← he, mem_sdiff, mem_union]
  exact ⟨fun hp => ⟨Or.inr hp,disjoint_left.mp hy hp⟩,
    fun h => h.1.resolve_left (fun hp => h.2 (hx hp))⟩

omit [Fintype V] in
private lemma disconnected_moment (B : Poly R) (a : Finset V) (i : R.Mode) :
    (dilation R (leftWeight a) B * dilation R (rightWeight a) B).part i =
      B.part (modeLeft i a) * B.part (modeRight i a) := by
  rw [Poly.part_mul,sum_eq_single (modeLeft i a)]
  · rw [sum_eq_single (modeRight i a)]
    · rw [if_pos (join_disconnected a i),left_project,right_project,if_pos (show
        (modeLeft i a).val⊆a from inter_subset_right),if_pos]
      exact disjoint_left.mpr fun x hx => (mem_sdiff.mp hx).2
    · intro y _ hy
      split
      next he =>
        rw [right_project, if_neg, mul_zero]
        exact fun hm => hy (join_unique a he inter_subset_right hm).2
      rfl
    simp
  · intro x _ hx
    apply sum_eq_zero; intro y _
    split
    next he =>
      rw [left_project,right_project]
      split
      next hi =>
        rw [if_neg (fun h => hx (join_unique a he hi h).1),mul_zero]
      rw [zero_mul]
    rfl
  simp

/-- If the *actual* joint moments on the relevant subsets of `t` factor between
two groups (this does not hold automatically for conditionally Gaussian variables
with random parameters!), then the joint cumulant vanishes. This is useful even
for factorization of data after a choice of Wick-connected vertex groups. -/
theorem connected_vanish_split (B : Poly R) (h : B.part R.quiet = 1)
    (t : R.Mode) (a : Finset V) (he : ¬ t.val ⊆ a) (hh : ¬ Disjoint t.val a)
    (hm : ∀ i : R.Mode, i.val ⊆ t.val → B.part i=B.part (modeLeft i a)*B.part (modeRight i a)) :
    (connected B).part t = 0 := by
  let L := dilation R (leftWeight a)
  let W := dilation R (rightWeight a)
  have ht : Anchor.UpTo t.val B (L B * W B) := fun i hi =>
    (hm i hi).trans (disconnected_moment B a i).symm
  rw [ht.conn t (Subset.refl _), connected_product (show (L B).part R.quiet=1 by
    unfold L; rw [dilation_part, h]; simp [Census.quiet]) (show (W B).part R.quiet=1 by
    unfold W; rw [dilation_part,h]; simp [Census.quiet]), Poly.part_plus]
  unfold L W
  rw [connected_dilation _ h, connected_dilation _ h, left_project, right_project,
    if_neg he, if_neg hh, zero_add]
end YM.Comparison.Cumulants
