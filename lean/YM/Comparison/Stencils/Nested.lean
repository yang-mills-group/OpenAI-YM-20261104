import YM.Comparison.Stencils.Letters

/-!
# Restriction maps for stencil letters

Supports and engineering horizons change separately. Bare anchors remain in
native lengths. Keep columns in their *own* horizons when needed. In
particular do not silently replace a cylinder at larger S/h by a different
cutoff observable just because their retained jet labels agree. The
`residual` below tells the consumer what *does* agree for such a
re-announcement, and gives actual finite symbols for the leftover. No bound on
its interacting RG transmission is claimed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Nested
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter Feed
open Next.Foundations
open Planned.PrimaryIntegral295.Place (Spot Dev)
open Push.Mark (cap_is capping)
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {S S' : Finset Cover}

section Support

lemma readdress (H : Hol G) (d : ℕ) (h : S ⊆ S') (p : LocalPol G S) :
    projector H d (raisePol G h p) = projector H d p := by
  refine sole_poly _ _ d (raw_cap ..) (raw_cap ..) (fun J i hi => ?_)
  change iteratedDeriv i (fun t => Labels.read (scaleJet J t) (rawPi H d _)) _ =
    iteratedDeriv i (fun t => Labels.read (scaleJet J t) (rawPi H d _)) _
  rw [jet_reads H d _ J i hi, jet_reads H d _ J i hi]; simp_rw [raisePol_value]

lemma same_booth (H : Hol G) (d i : ℕ) (h : S ⊆ S') (p : LocalPol G S) :
    booth H d i (raisePol G h p) = booth H d i p := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    let u := MvPolynomial.monomial a c
    let k := Finsupp.weight (fun _ => (1:ℕ)) a
    have he : Rank u k := MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
    have hp : Rank (raisePol G h u) k := by
      unfold u raisePol; rw [MvPolynomial.rename_monomial]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      -- Total ordinary rank regardless of injectivity.
      clear he
      induction a using Finsupp.induction_linear with
      | zero => simp [k]
      | add a b hx hy => simp only [k, Finsupp.mapDomain_add, map_add] at *; rw [hx,hy]
      | single i j => simp [Finsupp.weight_apply,k]
    rw [booth_one H d i hp, booth_one H d i he, readdress]
  | add p q hp hq => simp only [map_add,hp,hq]

lemma move_stage (H : Hol G) (d e : ℕ) (h : S ⊆ S') (P : LogSeries G S) :
    stage H d e (raisePol G h ∘ P) = stage H d e P := by
  simp_rw [stage_at, Function.comp_apply, same_booth]
end Support

section Horizon
variable {d e : ℕ}

lemma limited_agree (p : Pol G) (h : p ∈ limited G d) (J : Jet G) :
    Labels.read (expand d (trunk d J)) p = Labels.read J p := by
  have he (i : Key G →₀ ℕ) (k : Key G) (hp : k ∈ i.support) (hk : i ∈ p.support) : k.1 < d-1 := by
    have H : height i ≤ d := (MvPolynomial.mem_restrictSupport_iff ℂ).mp h hk
    have hu : generation k ≤ i k * generation k := le_mul_of_one_le_left (Nat.zero_le _)
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))
    have hv : i k * generation k ≤ height i := Finset.single_le_sum (f := fun j => i j * generation j)
      (fun _ _ => Nat.zero_le _) hp
    unfold generation at *; omega
  rw [p.as_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl; intro i hi
  simp only [Labels.read, MvPolynomial.aeval_monomial]
  congr 1
  exact Finset.prod_congr rfl fun k hk => by simp [Labels.coord, expand, trunk, he i k hk hi]

lemma scale_short (J : Jet G) (t : ℝ) (d : ℕ) :
    expand d (trunk d (scaleJet J t)) = scaleJet (expand d (trunk d J)) t := by
  funext i
  by_cases h : i < d-1 <;> simp [expand, trunk, scaleJet, h]

lemma limited_scale (p : Pol G) (h : p ∈ limited G d) (J : Jet G) :
    (fun t => Labels.read (scaleJet J t) p) =
      (fun t => Labels.read (scaleJet (expand d (trunk d J)) t) p) := by
  funext t
  rw [← scale_short, limited_agree _ h]

theorem transport_cap (H : Hol G) (h : d ≤ e) (J : Jet G) (t : ℝ) :
    H.links d (expand d (trunk d J)) t = H.links e (expand d (trunk d J)) t := by
  let Q := expand d (trunk d J)
  have he : potential d Q = potential e Q := by
    funext i x
    exact Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => by
      simp only [Finset.mem_range] at hj
      simp [Q, expand, hj, Taylor.value, Tensor.diagonal]
  have hk (p : Edge Cover) : partConnection d Q t p = partConnection e Q t p := by
    funext k; rw [partConnection, partConnection, he]
  funext p
  exact congr_fun ((H.solves d Q t p).unique (hk p ▸ H.solves e Q t p)) 1

lemma resize (H : Hol G) (h : d ≤ e) (p : LocalPol G S) :
    projector H d p = capRead d (projector H e p) := by
  let U := rawPi H d p
  let V := rawPi H e p
  refine sole_poly _ _ d (raw_cap ..) (cap_limited ..) (fun J k hk => ?_)
  let A := expand d (trunk d J)
  change iteratedDeriv k (fun t => Labels.read (scaleJet J t) U) 0 =
    iteratedDeriv k (fun t => Labels.read (scaleJet J t) (capRead d V)) 0
  rw [limited_scale _ (raw_cap H d p) J, limited_scale _ (cap_limited d V) J]
  change iteratedDeriv k (fun t => Labels.read (scaleJet A t) U) 0 =
    iteratedDeriv k (fun t => Labels.read (scaleJet A t) (capRead d V)) 0
  rw [jet_reads H d p A k hk, deriv_read A, tier_capRead d V k hk, ← deriv_read A,
    jet_reads H e p A k (hk.trans h)]; simp_rw [A, transport_cap H h J]

lemma resize_step (H : Hol G) (h : d ≤ e) (i : ℕ) (p : LocalPol G S) :
    booth H d i p = capRead d (booth H e i p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have H' := MvPolynomial.isWeightedHomogeneous_monomial (fun _ => (1:ℕ)) a c rfl
    rw [booth_one H _ _ H', booth_one H _ _ H', resize H h, cap_portion]
  | add p q hp hq => rw [map_add, map_add, hp, hq]; simp only [cap_is, map_add]

theorem projection_restriction (H : Hol G) (h : d ≤ e) (u : ℕ) (P : LogSeries G S) :
    stage H d u P = capRead d (stage H e u P) := by
  simp_rw [stage_at]; simp_rw [cap_is, map_sum]; apply Finset.sum_congr rfl
  intro i _; rw [resize_step H h, cap_is]
end Horizon

section Residual
variable (F : Frames G) (H : Hol G) (T : ∀ d, SectionData (F.level d))

/-- Re-announcement of a bare unscaled log-symbol column at a common
support; multiply by any needed extra length factors separately.
Slot/g normalization relative to the stencil's own announcement (including
which frame basis elements occur).
-/
def carryTo (d : ℕ) (p : Label G d) (S : Finset Cover) (hS : (T d).stencil ⊆ S) :
    Feed.LogSeries G S := raisePol G hS ∘ columns (T d) ((F.level d).coords p)

lemma remains {d : ℕ} (i : ℕ) (h : (T d).Sound H) (he : Bid.pop (T d)) (p : Label G d)
    (hS : (T d).stencil ⊆ S) :
    stage H d i (carryTo F T d p S hS) = if i=0 then p.val else 0 := by
  rw [carryTo, move_stage, normalization _ _ h he, LinearEquiv.symm_apply_apply]

/-- Symmetry-preserving canonical path changes on a support may nevertheless
shift the observable. This is the full operator-vertex difference (in common
units of links/threshold convention `S(g)`, before normalizing columns against
measurements). Such differences can't just be discarded. -/
def residual {d e : ℕ} (w : d ≤ e) (p : Label G d)
    (hS : (T d).stencil ⊆ S) (ht : (T e).stencil ⊆ S) : Feed.LogSeries G S :=
  carryTo F T d p S hS - carryTo F T e (raiseLabel G w p) S ht

theorem horizon_difference {d e : ℕ} (w : d ≤ e) (p : Label G d)
    (hS : (T d).stencil ⊆ S) (ht : (T e).stencil ⊆ S)
    (hs : ∀ d, (T d).Sound H) (hp : ∀ d, Bid.pop (T d)) (j : ℕ) :
    stage H d j (residual F T w p hS ht) = 0 ∧
      capRead d (stage H e j (residual F T w p hS ht)) = 0 := by
  rw [← projection_restriction H w, and_self]
  rw [residual, map_sub, remains F H T _ (hs _) (hp _), projection_restriction H w,
    remains F H T _ (hs _) (hp _)]
  split_ifs
  · change p.val - capRead d p.val = 0
    rw [limited_cap _ _ (show p.val ∈ limited G d from p.property.1), sub_self]
  simp [capRead]
end Residual
end YM.Comparison.Stencils.Nested
