import YM.RG11Proof.Bridge.Step
import YM.RG11Proof.Horizon.Mesh

/-!
# Rate bridge on one finite comparison regulator

This is a CONSUMER theorem (common-regulator algebra and propagation, not
the external bridge on Yang--Mills). From simultaneous `Saves` representations
including unknown coefficient multipliers and quantitative power-budget regulator
inputs on compact tested profiles, prove that the raw finite-order coupling and
field-matrix coefficients tend to the *same* detector solution at budget-rate,
that simultaneous transformed readings match within this budget and that the
independent continuum arrays convert exactly on the marked tests. No denominator
or volume cost omitted internally by the solver; any already spent to prove
these regulator/service premises must be retained in k's E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bridge
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal YM.RG11.Rate YM.RG11.Horizon Filter
open scoped Topology BigOperators Classical

variable {J P α : Type*} [Fintype J] [DecidableEq J] {shape:P→ℕ}
variable {k : Budget α} {L : Constraints ℝ J} {A B : ArrayAt J ℝ shape}
variable {V D : α→ArrayAt J ℝ shape} {T : α →Change ℝ J} {M n : ℕ} {m:Finset (Mark J shape)}

-- Common regulator contract just at tested smeared correlations. Choose
-- `m` to include degree-one coupling rows and free detector, plus as many more
-- profiles as requested. Need inside demand for ALL slot rows used after frame
-- change, and simultaneous residual attachments. Extend into geometries by
-- quantifying those profiles inside P, paying the rates & demanding actual
-- comparator's uniformity first. T(a) is a coefficient-by-coefficient cover
-- move in bare auxiliary coupling; near-leading estimates not tied to any
-- all-order boundedness. Require leading T.g derivative tends constant λ≠0
-- (or include external slope from independent calculation; see `finite_match`).
structure RegControl (k : Budget α) (M : ℕ) (m : Finset (Mark J shape))
    (A B : ArrayAt J ℝ shape) (V D : α→ArrayAt J ℝ shape)
    (L : Constraints ℝ J) (T : α→Change ℝ J) : Prop where
  usingAll : Nonempty (Saves k M m V D T)
  pivot {v} : v∈m → ∀ w,Crest k M V A (⟨v.1,w⟩:Mark J shape)
  columns {v} : v∈m → Crest k M D B v
  start (a) : Anchored (T a).g
  frame0 (i j) : Near k (fun a=>piece 0 (T a).Z i j) ((1:Square J ℝ) i j)
  -- Approximate variation suffices; CEOs can set `x a` to the raw
  -- coefficients exactly when filtering/equivariance and unit laws hold
  -- exactly. No closeness to the desired *solution coefficients* in this
  -- hypothesis, only closeness to the permitted frame and unit Lie *space*.
  variations {i : ℕ} : 0 < i → i ≤ M → ∃ x, Current L k T i x

namespace RegControl
variable (C : RegControl k M m A B V D L T) {Q : Detector L A} (hQ : TestDemand Q ⊆ m)
include C hQ

-- price all degrees through the announced order, arbitrary constants may
-- depend on that order and the finite m/D/their shape and color bases.
theorem older : Older (M+1) k T (solution Q B) := by
  have h := solution_law Q B
  suffices ∀ n ≤ M, Older (n+1) k T (solution Q B) from this _ le_rfl
  intro n hn
  induction n with
  | zero =>
    constructor
    · intro i hi; obtain rfl : i=0 := by omega
      simp_rw [coeff_zero_eq_constantCoeff_apply, show ∀ a, constantCoeff (T a).g=0 from C.start,
        show constantCoeff (solution Q B).g=0 from h.1]
      exact Near.const 0
    intro i hi; obtain rfl : i=0 := by omega
    rw [h.2.baseline]; exact C.frame0
  | succ n hh =>
    obtain ⟨x,hX⟩:= C.variations n.zero_lt_succ hn
    exact newer Q x n.zero_lt_succ hn hX C.start (Classical.choice C.usingAll) hQ (fun i hi j=> (C.pivot hi j).of_le hn)
        (fun i hi=> (C.columns hi).of_le hn) (hh (by omega))

/-- Quantitative finite-order result, including the transferred correlation
pieces on the requested marks. -/
structure Pays (k : Budget α) (M : ℕ) (m : Finset (Mark J shape))
    (A B : ArrayAt J ℝ shape) (V D : α→ArrayAt J ℝ shape) (p : Change ℝ J) (T : α→Change ℝ J) : Prop where
  rulers : Pieces k M (fun a=> (T a).g) (fun _=>p.g)
  fields (i j) : Pieces k M (fun a=> (T a).Z i j) (fun _=>p.Z i j)
  raw {v} : v∈m → Pieces k M (fun a=>(T a).act (V a) v) (fun _=>p.act A v)
  converted {v} : v∈m → Pieces k M (fun a=>D a v) (fun _ => p.act A v)
  -- The input bound itself listed for the identification lemma.
  external {v} : v∈m → Crest k M D B v

omit C hQ in
private theorem prodPieces {I : Type*} {p q:I→α→PowerSeries ℝ} (s:Finset I) (H : ∀ i∈s, Pieces k M (p i) (q i)) :
    Pieces k M (fun a=> ∏ i∈s,p i a) (fun a=> ∏ i∈s,q i a) := by
  classical
  induction s using Finset.induction_on with
  |empty=>simp
  |insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (H _ (by simp)).mul (ih (fun j hj=>H _ (by simp [hj])))
-- remove implicit unused J below

/-- Derive the displayed quantitative budgets, then all test identities without
interchanging UV and expanding-geometry limits. -/
theorem pays : Pays k M m A B V D (solution Q B) T := by
  let p:= solution Q B
  have he := C.older hQ
  have hL : Pieces k M (fun a=> (T a).g) (fun _=>p.g) := Pieces.tight (fun i hi=> he.1 _ (by omega))
  have hE(i j:J) : Pieces k M (fun a=>(T a).Z i j) (fun _=>p.Z i j):= Pieces.tight (fun l hl=> he.2 _ (by omega) i j)
  let e := Classical.choice C.usingAll
  have hRaw (v : Mark J shape) (hv : v∈m) : Pieces k M (fun a=>(T a).act (V a) v) (fun _=>p.act A v) :=
    Pieces.sum Finset.univ (fun w _=> ((C.pivot hv w).compose hL C.start (fun _=> (solution_law ..).1)).mul (prodPieces _ (fun _ _=>hE _ _))) -- linter unused i?
  refine ⟨hL,hE,fun {v} hv=>hRaw v hv,?_,fun hv=> C.columns hv⟩
  intro v hv
  have hT : Pieces k M (fun a=> tail (e.bits a) (T a).Z v) (fun _=> tail (fun _ _ _=>0) p.Z v) := by
    refine Pieces.sum _ (fun s _=> ?_)
    by_cases hs : s=∅
    · simp only [hs,↓reduceIte]; exact Pieces.const _
    simp only [if_neg hs]
    exact Pieces.sum _ (fun w _=>Pieces.mul (e.slips hv s (Finset.nonempty_iff_ne_empty.mpr hs) w) (prodPieces _ (fun _ _=>hE _ _)))
  have hw := (hRaw v hv).add hT
  have ht : tail (fun _ _ _=>0) p.Z v = (0:PowerSeries ℝ) := by simp [tail]
  simp_rw [ht,add_zero] at hw
  exact Pieces.tight (fun i hi=> NearFn.turnsNear (e.values hi v hv) (hw.price hi))

omit [DecidableEq J] C hQ in
theorem Pays.identifies [k.along.NeBot] {p} (h : Pays k M m A B V D p T) : OnMarks M m B (p.act A) := by
  intro v hv i hi
  exact Near.identify (h.external hv |>.price hi) (h.converted hv |>.price hi)

-- Branch/tangent pin via the finite-regulator linear coefficient (can even
-- be an o(1) transfer to a nonzero tangent instead of O(E) here).
omit [DecidableEq J] C hQ in
theorem Pays.nonsingular [k.along.NeBot] {p} (h : Pays k M m A B V D p T) (hM : 1≤M) (c : ℝ)
    (hc : c ≠ 0) (he : Tendsto (fun a=>coeff 1 (T a).g) k.along (𝓝 c)) : IsUnit (tangent p.g):= by
  have hz : Near k (fun a=> coeff 1 (T a).g) (tangent p.g):=h.rulers.price hM
  rw [tendsto_nhds_unique hz.small he]; exact isUnit_iff_ne_zero.mpr hc

-- One instance per requested order and demand. This gives the SAME solution
-- that any previously fitted (at overlapping tests through a larger enough)
-- bridge would give. If M=0 require a first-order bridge for the detector
-- only, and glue/restrict (`Horizon.Mesh`).
theorem finite_match [k.along.NeBot] (hM:1≤M) (x : ℝ) (hx : x≠0)
    (he : Tendsto (fun a=>coeff 1 (T a).g) k.along (𝓝 x)) :
    Change.Good L (solution Q B) ∧ OnMarks M m B ((solution Q B).act A) := by
  let p:=solution Q B
  have hv : Pays k M m A B V D p T := pays C hQ
  exact ⟨⟨⟨(solution_law Q B).1,hv.nonsingular hM x hx he⟩,(solution_law Q B).2⟩,hv.identifies⟩
end RegControl
end YM.RG11.Bridge
