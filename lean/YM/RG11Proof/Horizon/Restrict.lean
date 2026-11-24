import YM.RG11Proof.Formal.Orbit

/-!
# Restricting a change to a smaller field horizon

The position detector needed at a small horizon is *not* reconstructed by
arbitrary choices from tests at an unrelated horizon. Instead, on coherent
independent array inputs and a matched solution, restrict along specified basis
embeddings and use the finite uniqueness theorem. Need in production:
each comparison through requested order for arbitrary large finite horizons
(including any chosen determining ones). No Fintype or Gram constants uniform
in that horizon are asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Horizon
open PowerSeries YM.PertExtension.Position YM.RG11.Formal YM.RG11.Jets
open scoped Classical BigOperators

variable {J K L R S : Type*} (ι : J ↪ K) [Fintype J] [Fintype K] [Fintype L]

/-- Change respects the embedding's subspace (not a projection that may mix
before summing). Works for pieces over ℝ, matrices over FPS, etc. -/
def Held [Zero R] (ι : J ↪ K) (A : Square K R) : Prop :=
  ∀ (i:J) (j:K), j ∉ Set.range ι → A (ι i) j=0

def take (ι : J ↪ K) (A : Square K R) : Square J R:= A.submatrix ι ι

omit [Fintype J] [Fintype K] in
@[simp] theorem take_apply (A : Square K R) (i j) : take ι A i j=A (ι i) (ι j):=rfl

omit [Fintype J] [Fintype K] in
@[simp] theorem take_one [DecidableEq J] [DecidableEq K] [One R] [Zero R] :
    take ι (1:Square K R)=(1:Square J R) := by
  ext i j; simp [Matrix.one_apply]

-- Summation by down-supported rows along the embedding; no monotonicity of
-- the other rows is needed.
private theorem sum_embedding [AddCommMonoid R] (f : K→R) (hp : ∀ k, k∉ Set.range ι → f k=0) :
    ∑ k, f k = ∑ i, f (ι i) := by
  classical
  rw [← Finset.sum_map (Finset.univ (α:=J)) ι f]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ he=> hp k (fun ⟨i,hi⟩=> he (hi ▸ Finset.mem_map_of_mem _ (Finset.mem_univ i))))).symm

theorem take_mul [Semiring R] {A B : Square K R} (h : Held ι A) :
    take ι (A*B)=take ι A*take ι B := by
  ext i j
  simp only [take_apply,Matrix.mul_apply]
  exact sum_embedding _ _ fun k hk=> by rw [h i k hk,zero_mul]

omit [Fintype J] [Fintype K] in
@[simp] theorem take_piece [Semiring R] (n : ℕ) (A : Square K R⟦X⟧) :
    take ι (piece n A)=piece n (take ι A):=rfl

omit [Fintype J] [Fintype K] in
@[simp] theorem take_subs [CommRing R] (p : R⟦X⟧) (A : Square K R⟦X⟧) :
    take ι (subs p A)=subs p (take ι A) := rfl

theorem take_squareInv [Ring R] [DecidableEq J] [DecidableEq K] {A : Square K R⟦X⟧} (ha : nearId A)
    (h : Held ι A) : take ι (squareInv A) = squareInv (take ι A) := by
  have hb : take ι A * take ι (squareInv A) = 1 := by rw [← take_mul _ h,mul_squareInv ha,take_one]
  have hh : nearId (take ι A) := (take_piece ι ..).symm.trans (Eq.trans (congrArg (take ι) ha) (take_one _))
  exact (left_inv_eq_right_inv (squareInv_mul hh) hb).symm

variable {P : Type*} {shape : P→ℕ}

def view (v : Mark J shape) : Mark K shape:= ⟨v.1,fun i=>ι (v.2 i)⟩
def slice {P : Type*} {shape : P→ℕ} (A : ArrayAt K R shape) : ArrayAt J R shape:= fun v=> A (view ι v)

private def piEmb {n : ℕ} : (Fin n→J) ↪ (Fin n→K):=
  ⟨fun f i=>ι (f i), fun _ _ h=> funext fun _=> ι.injective (congrFun h _)⟩

theorem take_insert [CommSemiring R] (B : Mark K shape→R) {Z : Square K R} (h : Held ι Z)
    (v : Mark J shape) :
    PertExtension.Position.insert K shape B (fun i j=>Z i j) (view ι v)=
    PertExtension.Position.insert J shape (fun w=>B (view ι w)) (fun i j=>take ι Z i j) v := by
  classical
  trans (∑ w: Fin (shape v.1)→J, B ⟨v.1,ι∘w⟩ * ∏ i,Z (ι (v.2 i)) (ι (w i)))
  · refine sum_embedding (piEmb (n:=shape v.1) ι)
       (fun w=> B ⟨v.1,w⟩ * ∏ i,Z (ι (v.2 i)) (w i)) ?_
    intro w he
    have hV : ∃ i, w i ∉ Set.range ι := not_forall_not.mp fun hf=> by
      choose t ht using fun i=> (show ∃ x, ι x=w i from not_not.mp (hf i))
      exact he ⟨t,funext ht⟩
    obtain ⟨i,hi⟩:=hV
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (h _ (w i) hi),mul_zero]
  rfl

def restrict [CommRing R] (c : Change R K) : Change R J := ⟨c.g,take ι c.Z⟩

theorem slice_action [CommRing R] {A : ArrayAt K R shape} {c : Change R K} (h : Held ι c.Z) :
    slice ι (c.act A) = (restrict ι c).act (slice ι A) := funext fun v=>
  take_insert _ (fun v=>PowerSeries.subst c.g (A v)) h v

variable (ω : K ↪ L)

omit [Fintype J] [Fintype K] [Fintype L] in
@[simp] theorem view_view (v : Mark J shape) : view ω (view ι v)=view (ι.trans ω) v:=rfl
omit [Fintype J] [Fintype K] [Fintype L] in
@[simp] theorem slice_slice (A : ArrayAt L R shape) : slice ι (slice ω A)=slice (ι.trans ω) A:=rfl
omit [Fintype J] [Fintype K] [Fintype L] in
@[simp] theorem take_take (A : Square L R) : take ι (take ω A)=take (ι.trans ω) A := rfl

-- Instead of presuming that (e.g.) exactly the same lifted basis appears
-- in all schemes, export each condition needed on the chosen injections.
section coherent
variable [CommRing R] [DecidableEq J] [DecidableEq K] {U : Constraints R J} {V : Constraints R K}

/-- This is a check on concrete filtration lifts, not a license to truncate
operator counterterms (e.g. evanescent/BRST/EOM families have to be handled
in the reference prescription first). -/
structure Coherent (U : Constraints R J) (V : Constraints R K) : Prop where
  anchored (M : V.vary) : Held ι M.val
  legal (M : V.vary) : take ι M.val ∈ U.vary

namespace Coherent
theorem lawful {A : Square K R⟦X⟧} (h : Coherent ι U V) (hc : V.Lawful A) : U.Lawful (take ι A) where
  baseline := (take_piece ι ..).symm.trans (Eq.trans (congrArg (take ι) hc.baseline) (take_one _))
  positive {i} hi := (take_piece ι i A) ▸ h.legal (⟨piece i A,hc.positive hi⟩:V.vary)

omit [DecidableEq J] in
theorem allHeld {A : Square K R⟦X⟧} (h : Coherent ι U V) (hc : V.Lawful A) : Held ι A := by
  intro i j hj
  apply PowerSeries.ext; intro n; rw [map_zero, ← piece_apply (A:=A), show (piece n A (ι i) j)=0 from ?_]
  cases n with
  | zero => rw [hc.baseline]; exact Matrix.one_apply_ne fun he=>hj ⟨i,he⟩
  | succ n => exact h.anchored ⟨_,hc.positive (i:=n+1) (by omega)⟩ i j hj


theorem good {c : Change R K} (h : Coherent ι U V) (hc : Change.Good V c) : Change.Good U (restrict ι c) :=
  ⟨hc.ruler, lawful ι h hc.field⟩
end Coherent
end coherent
end YM.RG11.Horizon
