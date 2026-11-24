import YM.RG11Proof.Horizon.Quotient

/-!
# Glueing arbitrarily large finite matches

Even a common-regulator proof might only work at demands (finite P-tests,
power truncations, field horizons) whose period/scale thresholds depend on
them all. Do *not* require a single sequence of finite cutoff conversions to
become coefficientwise bounded at all these demands simultaneously! Detector
uniqueness supplies the desired compatible limiting choice from matches
local in all three indices. Conversely this theorem is formal *only* and
doesn't transfer rate or uniformity to varying demands in the actual theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Horizon
open PowerSeries YM.PertExtension.Position YM.RG11.Jets YM.RG11.Formal
open scoped Classical BigOperators

section arity
variable {J R P : Type*} [Field R] [Fintype J] [DecidableEq J]
variable {shape : P→ℕ} {L : Constraints R J} {A B : ArrayAt J R shape}

-- Every test tag `v` here is the whole normalized reading (not one leg
-- without partners); transform requires also matching EVERY row at that same
-- P-coordinate for some uses, but uniqueness needs only these *output* v's.
def OnMarks (n : ℕ) (m : Finset (Mark J shape)) (B A : ArrayAt J R shape) :=
  ∀ v∈m, Through n (B v) (A v)

def FiniteComparison (L : Constraints R J) (A B : ArrayAt J R shape) (n : ℕ) : Prop :=
  ∀ m : Finset (Mark J shape), ∃ c : Change R J, Change.Good L c ∧ OnMarks n m B (c.act A)

-- Uniqueness proof reused; thus the actual solve is order- and test-coherent.
theorem forced_output (D : Detector L A) {n} (h : FiniteComparison L A B n) :
    ArrayThrough n B ((solution D B).act A) := by
  classical
  intro v
  obtain ⟨c,hg,H⟩ := h (Insert.insert v (Finset.univ.image D.test))
  have he : c.EquivJet (solution D B) n := uniqueness D B ⟨hg.ruler.base,hg.field⟩ (solution_law D B) n
     (fun i hi _=> congrArg D.restore (funext fun t=>H _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ t))) i hi))
     (fun _ _=> hits D B)
  exact (H _ (Finset.mem_insert_self ..)).trans (he.act hg.ruler.base (fun _=> Through.refl _))

theorem forced_good (D : Detector L A) {n} (hn:1≤n) (h : FiniteComparison L A B n) : Change.Good L (solution D B) := by
  classical
  obtain ⟨c,hg,H⟩:=h (Finset.univ.image D.test)
  have he : c.EquivJet (solution D B) n := uniqueness D B ⟨hg.ruler.base,hg.field⟩ (solution_law D B) n
    (fun i hi _=> congrArg D.restore (funext fun t=> H _ (Finset.mem_image_of_mem _ (Finset.mem_univ t)) i hi)) (fun _ _=> hits D B)
  exact ⟨⟨(solution_law D B).1, by unfold tangent; rw [← he.ruler 1 hn]; exact hg.ruler.nonsingular⟩,
        (solution_law D B).2⟩

/-- Convenient all-orders at fixed field test sector. -/
theorem forced (D : Detector L A) (h : ∀ n, FiniteComparison L A B n) :
    Change.Good L (solution D B) ∧ B=(solution D B).act A :=
  ⟨forced_good D (n:=1) le_rfl (h _),funext fun v=>PowerSeries.ext fun n=> forced_output D (h n) v n le_rfl⟩
end arity

section bundle
variable (R : Type*) [Field R] {P : Type*} (shape : P→ℕ)
universe u
/-- The same filtered engineering field-horizon system and two arrays on
it. `0` stands for the *least horizon needed for detection*, e.g. through
weight 6, then every n adds (nondecreasing) fields. Use with the chosen basis
of physical separated quotient; system must remain compatible across tests *as
defined* (coherence of `V`, `A`, `B` exported separately). This does not
shrink any physical demands below that least one. -/
structure Mesh where
  J : ℕ→Type u
  count n : Fintype (J n)
  requests n : @Constraints R (J n) _ (count n)
  rise {n m:ℕ} : n ≤ m → J n ↪ J m
  same (n) : rise (le_refl n)=Function.Embedding.refl (J n)
  together {n m k} (h:n ≤ m) (q:m ≤ k) : (rise h).trans (rise q)=rise (le_trans h q)
  A (n:ℕ) : ArrayAt (J n) R shape
  B (n:ℕ) : ArrayAt (J n) R shape

attribute [instance] Mesh.count
variable {R shape}
namespace Mesh
variable (M : Mesh R shape)

structure Steady : Prop where
  sensors {n m:ℕ} (h:n ≤ m): Coherent (M.rise h) (M.requests n) (M.requests m)
  smallA {n m:ℕ} (h:n ≤ m): slice (M.rise h) (M.A m)=M.A n
  smallB {n m:ℕ} (h:n ≤ m): slice (M.rise h) (M.B m)=M.B n

-- `DecidableEq` not part of mesh comparison data.
def Cofinal (M : Mesh R shape) := ∀ n k,
    ∃ N, n≤N ∧ ∃ K, k≤K ∧ FiniteComparison (M.requests N) (M.A N) (M.B N) K

/-- One jointly constructed formal conversion, incl a single coupling.
The family is actual FPS purely to encode coherence; there is no assertion
the series converge near 0. -/
structure Reports where
  c (n:ℕ) : Change R (M.J n)
  good n : Change.Good (M.requests n) (c n)
  answers n : M.B n=(c n).act (M.A n)
  matched {n m} (h:n ≤ m) : restrict (M.rise h) (c m)=c n

variable (D : ∀ n : ℕ, Detector (M.requests n) (M.A n)) (hV : Steady M) (h : Cofinal M)

def stable (n:ℕ) : Change R (M.J n) := solution (D n) (M.B n)

include hV h D
theorem each (n:ℕ) (k:ℕ) : FiniteComparison (M.requests n) (M.A n) (M.B n) k := by
  classical
  obtain ⟨N,hN,K,hK,hk⟩:=h n (max k 1)
  let q:=solution (D N) (M.B N); have hQ : Change.Good (M.requests N) q:= forced_good (D N) (n:=K) (by omega) hk
  let c:=restrict (M.rise hN) q
  have he : ArrayThrough k (M.B n) (c.act (M.A n)) :=
    Coherent.array (L:=M.requests n) _ (n:=K) ((le_max_left ..).trans hK) (hV.sensors hN) ⟨hQ.ruler.base,hQ.field⟩
       (by rw [hV.smallA]; exact ArrayThrough.refl) (by rw [hV.smallB]; exact ArrayThrough.refl) (forced_output (D N) hk)
  exact fun _=> ⟨c, Coherent.good _ (hV.sensors hN) hQ, fun v _=>he v⟩ -- D unused? autoimplicit

theorem stable_result (n:ℕ) : Change.Good (M.requests n) (stable M D n) ∧ M.B n=(stable M D n).act (M.A n) := forced (D n) (each M D hV h n) -- D not included above?

def obtainReports : Reports M where
  c := stable M D
  good n := (stable_result M D hV h n).1
  answers n := (stable_result M D hV h n).2
  matched {n m} hm := by
    have Hu:=stable_result M D hV h m
    have Hq(k) : (restrict (M.rise hm) (M.stable D m)).EquivJet (M.stable D n) k := by
      apply Coherent.solution_down _ (D n) (A':=M.A m) (B':=M.B m) (hV.sensors hm) ⟨Hu.1.ruler.base,Hu.1.field⟩
      · rw [hV.smallA]; exact ArrayThrough.refl
      · rw [hV.smallB]; exact ArrayThrough.refl
      rw [Hu.2]; exact ArrayThrough.refl
    ext <;> first|exact (Hq _).ruler _ le_rfl| exact (Hq _).field _ _ _ le_rfl
end Mesh
end bundle
end YM.RG11.Horizon
