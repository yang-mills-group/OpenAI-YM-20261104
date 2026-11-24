import YM.FormalOPE.RG10.Routes.Legs

/-!
# MvPolynomial kernels with all external legs retained

Order-by-order identity for forest pieces *after integrating and normalizing*. Read as a
coarse/profile kernel; no Leg multiplicity shortcuts. Evaluate on the identical data for every y,
not pointwise different `W` vertices or representations during pricing of a norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open MvPolynomial Finset Marker Extra.Trajectories Joins Joins.Gauss Function
open Multi (parts shards)
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I J B V K : Type} [Fintype J] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (q : I→Row J)
local notation "F" => standardFeed J
local notation "H" => hall J
section primal
variable {R : Census V} (s : R.Mode) (p : V→ Packet (I ⊕ B))

/-- Taylor moment contribution to the polynomial (for ALL possible external legs of the indicated
ancestral vertex set). -/
def TallyRow (f : ↥s.val→ Index I B) := award F H (accepted J) s fun i : ↥s.val => leaking q (glyph (fine (f i)))

def sketch (f : ↥s.val→Index I B) : Packet B := monomial (∑ i, coarse (f i))
      ((∏ i, coeff (f i) (p i.val))* TallyRow q s f)

-- possibilities ONLY for these actually present

def streets := Fintype.piFinset fun i : ↥s.val => (p i.val).support

def track : Packet B := ∑ f ∈ streets s p, sketch q s p f

variable (y : B→ℂ)
lemma sketch_exact (f) : aeval y (sketch q s p f)=
    award F H (accepted J) s fun i : ↥s.val => study q y (monomial (f i) (coeff (f i) (p i.val))) := by
  unfold sketch; simp_rw [rolled]; rw [MultilinearMap.map_smul_univ];
  simp only [smul_eq_mul]
  let a (i : ↥s.val):= coeff (f i) (p i.val)
  let g (i : ↥s.val):= coarse (f i)
  have he (c' : ℂ) (j : Letters B) : aeval y (monomial j c' : Packet B) = c'*aeval y (glyph j) := by unfold glyph; rw [aeval_monomial,aeval_monomial]; rw [map_one,one_mul]; rfl
  change aeval y ((monomial (∑ i, g i)) ((∏ i, a i)*TallyRow q s f) : Packet B) = (∏ i, aeval y (monomial (g i) (a i) : Packet B))*TallyRow q s f
  rw [he, glyph_prod]; simp_rw [he]; rw [Finset.prod_mul_distrib]; ring
end primal
section web
variable {R : Census V} (W : (B→ℂ) → Vertices (Unit× Row J)) (A : (B→ℂ) → Unit× Row J → Word R)
local notation "T" => Polar.budget R K
variable (g : Payload K R → Packet (I ⊕ B))

/-- Equality of actual row calculus, before pricing. Can be verified given the stipulated local
kernels, Gaussian/Taylor law and exact source polynomials, even with multiple insertions or none.
Does not ask for norm bounds on outputs. -/
def Parsed : Prop := ∀ y, Performs (W y) K (A y) (fun v => (study q y (g v)).val)

theorem locate (y : B→ℂ) (hp : Parsed q W A g) (s : R.Mode) (hs : s.val.Nonempty) (hv : Word.read R.quiet (A y)=1)
    (k : Finset K) :
    aeval y (∑ i∈shards T (Polar.pay s k), track q i g) =
      (k.card.factorial:ℂ)*PowerSeries.coeff k.card (Word.see s ((F).contraction (W y) (A y))) := by
  let e := fun i : Payload K R => (g i).support
  let f := fun p : Payload K R => fun v => study q y (monomial v (coeff v (g p)))
  have he : (fun v=>(study q y (g v)).val) = actor H e f := by
    funext v; unfold actor; nth_rw 1 [as_sum (g v)]; rw [map_sum]
  rw [map_sum, linked F (W y) H (accepted J) e (A y) f (he ▸ hp y) hv s hs k]
  apply Finset.sum_congr rfl; intro i _; rw [track, map_sum]; exact sum_congr rfl fun w _ => sketch_exact q i g y w
end web
end YM.FormalOPE.RG10.Route
