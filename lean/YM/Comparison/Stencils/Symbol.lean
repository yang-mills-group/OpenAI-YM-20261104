import YM.Comparison.Stencils.PathSeries
import YM.Planned.PRIMARY_INTEGRAL_295.Columns

/-!
# Local polynomial symbols in log-link coordinates

Use ordinary commuting variables on all links (including any external or
fixed ones when reading a primitive). The MvPolynomial representation allows
complexification by substitution without pretending that the real group is
complex. Use the same labels for *order-zero* Gaussian contractions and for
higher Taylor calculation; no Wick ordering is done by `symbol`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Symbols
open CubicMatch Function Lattice Wilson Gauge
open Planned.PrimaryIntegral295.Place
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

section Rank
variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Rank in the present coordinates only. We'll use it before and *also*,
separately, after changing to radial variables. -/
abbrev Rank := MvPolynomial.IsWeightedHomogeneous (R := R) (fun _ : σ => (1 : ℕ))
def portion (k : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  MvPolynomial.weightedHomogeneousComponent (fun _ : σ => (1 : ℕ)) k

lemma rank_slot (p : MvPolynomial σ R) (n : ℕ) : Rank p n ↔
    ∀ m ∈ p.support, slots m = n := by
  rw [Rank, MvPolynomial.IsWeightedHomogeneous]
  simp only [MvPolynomial.mem_support_iff, slots]
  simp [Finsupp.weight_apply]

lemma portion_in (p : MvPolynomial σ R) (n : ℕ) : Rank (portion n p) n :=
  MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _

lemma on_rank (p : MvPolynomial σ R) (n : ℕ) (h : Rank p n) (m : ℕ) :
    portion m p = if m = n then p else 0 :=
  MvPolynomial.weightedHomogeneousComponent_of_mem h

lemma portion_coeff (p : MvPolynomial σ R) (n : ℕ) (a : σ →₀ ℕ) :
    (portion n p).coeff a = if slots a = n then p.coeff a else 0 := by
  rw [portion, MvPolynomial.coeff_weightedHomogeneousComponent]
  simp [Finsupp.weight_apply, slots]
end Rank

section Polarize
open Tensor
variable {σ ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (v : ι → E) (key : ι → σ)

/-- Concrete commuting polynomial formula from a real multilinear tensor,
including zero-slot scalar. Use also with spare unused keys. -/
def stencilPol : (j : ℕ) → T E ℂ j → MvPolynomial σ ℂ
  | 0, A => MvPolynomial.C (diagonal A 0)
  | j+1, A => ∑ i : ι, MvPolynomial.X (key i) * stencilPol j (A.curryLeft (v i))

lemma stencilPol_rank (j : ℕ) (A : T E ℂ j) : Rank (stencilPol v key j A) j := by
  induction j with
  | zero => rw [stencilPol]; exact MvPolynomial.isWeightedHomogeneous_C _ _
  | succ j ih =>
    rw [stencilPol]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro i _
    have h := ((MvPolynomial.isWeightedHomogeneous_X ℂ (fun _ : σ => (1:ℕ)) (key i)).mul (ih (A.curryLeft (v i))))
    rwa [Nat.add_comm (1:ℕ)] at h

lemma stencilPol_value (j : ℕ) (A : T E ℂ j) (x : E) (y : σ → ℂ) (r : ι → ℝ)
    (hx : x = ∑ i : ι, r i • v i) (hy : ∀ i, y (key i) = ↑(r i)) :
    MvPolynomial.aeval y (stencilPol v key j A) = diagonal A x := by
  induction j with
  | zero =>
    rw [stencilPol, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply]
    exact congrArg A (Subsingleton.elim ..)
  | succ j ih =>
    have hc : A.curryLeft x = ∑ i : ι, r i • A.curryLeft (v i) := by rw [hx, map_sum]; simp
    have e : diagonal A x = diagonal (A.curryLeft x) x := by
      apply congrArg A; funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp
    rw [e, hc, diagonal, stencilPol, map_sum (MvPolynomial.aeval y)]
    rw [sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.aeval_X, ih, smul_apply, Complex.real_smul, hy]; rfl
end Polarize

variable {S S' : Finset Cover} {G : Gauge}
-- Borrow the log chart of `YM.Planned.PrimaryIntegral295.Place`. Both link
-- endpoints are inside S.
abbrev Var (G : Gauge) (S : Finset Cover) := Spot S × G.ColorIndex

abbrev LocalPol (G : Gauge) (S : Finset Cover) := MvPolynomial (Var G S) ℂ

def coordinate (k : Var G S) : Dev S G →L[ℝ] ℝ :=
  EuclideanSpace.proj k.2 ∘L ContinuousLinearMap.proj k.1
lemma coordinate_value (k : Var G S) (x : Dev S G) : coordinate k x = x k.1 k.2 := rfl

def pinLink (k : Var G S) : Dev S G := Pi.single k.1 (EuclideanSpace.basisFun G.ColorIndex ℝ k.2)

lemma link_repr (x : Dev S G) : ∑ k : Var G S, (coordinate k x) • pinLink k = x := by
  classical
  funext e
  unfold Var at *
  rw [Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_eq_single e]
  · simp only [coordinate_value, pinLink, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
    exact (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (x e)
  · intro b _ hb; simp [pinLink, Finset.sum_apply, Pi.single_eq_of_ne hb.symm]
  simp

def inscribe (v : Dev S G) : LocalPol G S →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval fun i => ((coordinate i v : ℝ) : ℂ)

lemma inscribe_ext (P Q : LocalPol G S) (h : ∀ v, inscribe v P = inscribe v Q) : P = Q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun x : ℝ => (x : ℂ))) fun _ =>
    Set.infinite_range_of_injective Complex.ofReal_injective
  intro x hx
  choose y hy using fun k => hx k (Set.mem_univ k)
  let A : Dev S G := fun s => WithLp.toLp _ (fun i => y (s,i))
  rw [show x = fun i => ↑(coordinate i A) by funext i; exact (hy i).symm]
  exact h A

-- Free patches in front of perturbative integration. `A` can also be
-- tested on the cover without any periodicity.
def patch (S : Finset Cover) (A : Links ℤ G.Color) : Dev S G := A ∘ placeEdge

def widen (v : Dev S G) : Links ℤ G.Color := fun e =>
  if h : e.1 ∈ S ∧ e.1 + step e.2 ∈ S then v ⟨(⟨e.1,h.1⟩,e.2),h.2⟩ else 0

lemma drops (v : Dev S G) : patch S (widen v) = v := by
  funext e; exact dif_pos (show _ ∧ _ from ⟨(first e).property,e.property⟩)

lemma patch_agree (x : Links ℤ G.Color) (S : Finset Cover) :
    Agrees S (linksOf x) (pore (patch S x)) := by
  intro b h hb
  unfold pore; rw [dif_pos (show b.1∈S ∧ b.1+step b.2∈S from ⟨h,hb⟩)]
  rfl

lemma links_pore (v : Dev S G) : linksOf (widen v) = pore v := by
  funext b; unfold linksOf widen pore; split <;> simp

lemma as_logs (f : CoverConfig G → ℂ) (h : LocalOn S f) (x : Links ℤ G.Color) :
    f (linksOf x) = f (pore (patch S x)) := h _ _ (patch_agree x S)

def symbol (S : Finset Cover) (f : CoverConfig G → ℂ) (k : ℕ) : LocalPol G S :=
  stencilPol (pinLink (S := S) (G := G)) id k (Tensor.coeff (f ∘ pore) k 0)

lemma symbol_rank (S : Finset Cover) (f : CoverConfig G → ℂ) (k : ℕ) : Rank (symbol S f k) k :=
  stencilPol_rank ..

lemma symbol_patch (S : Finset Cover) (f : CoverConfig G → ℂ) (k : ℕ) (v : Dev S G) :
    inscribe v (symbol S f k) = Tensor.diagonal (Tensor.coeff (f ∘ pore) k 0) v :=
  stencilPol_value _ _ _ _ _ (fun i => ↑(coordinate i v)) _ (link_repr v).symm fun _ => rfl

theorem symbol_value (f : CoverConfig G → ℂ) (j : LocalOn S f) (A : Links ℤ G.Color) (k : ℕ)
    (h : ContDiffAt ℝ k (fun x : Dev S G => f (pore x)) 0) :
    inscribe (patch S A) (symbol S f k) = term k (fun t : ℝ => f (linksOf (t • A))) := by
  have e : (fun t : ℝ => f (linksOf (t • A))) = fun t => f (pore (t • patch S A)) :=
    funext fun t => as_logs f j _
  rw [symbol_patch, e]; exact (term_ray h _).symm

/-- We can reannounce with all paths/extra addresses on a larger support.
Support recall is an injection of polynomial variable alphabets; don't drop
stencil paths during an actual mask change. -/
def embedSpot (h : S ⊆ S') (i : Spot S) : Spot S' :=
  ⟨(⟨(first i).val, h (first i).property⟩, beam i), h i.property⟩

def raisePol (G : Gauge) (h : S ⊆ S') : LocalPol G S →ₐ[ℂ] LocalPol G S' :=
  MvPolynomial.rename fun i : Var G S => (embedSpot h i.1, i.2)

lemma raisePol_value (h : S ⊆ S') (P : LocalPol G S) (A : Links ℤ G.Color) :
    inscribe (patch S' A) (raisePol G h P) = inscribe (patch S A) P := by
  rw [inscribe, raisePol, MvPolynomial.aeval_rename]; rfl

lemma symbol_agree (h : S ⊆ S') (f : CoverConfig G → ℂ) (P : LocalOn S f) (k : ℕ)
    (h₀ : ContDiffAt ℝ k (fun x : Dev S G => f (pore x)) 0)
    (h₁ : ContDiffAt ℝ k (fun x : Dev S' G => f (pore x)) 0) :
    raisePol G h (symbol S f k) = symbol S' f k := by
  have he : LocalOn S' f := fun U V he => P U V fun x hx hx' => he x (h hx) (h hx')
  apply inscribe_ext
  intro v
  let A := widen v
  calc
    _ = inscribe (patch S' A) (raisePol G h (symbol S f k)) := congrArg
          (fun w => inscribe w (raisePol G h (symbol S f k))) (drops v).symm
    _ = term k (fun t : ℝ => f (linksOf (t • A))) :=
      (raisePol_value h (symbol S f k) A).trans (symbol_value f P _ k h₀)
    _ = inscribe v (symbol S' f k) := (symbol_value f he _ k h₁).symm.trans
          (congrArg (fun x => inscribe x (symbol S' f k)) (drops v))
end YM.Comparison.Stencils.Symbols
