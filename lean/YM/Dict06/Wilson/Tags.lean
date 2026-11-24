import YM.Dict06.Wilson.PowerRead
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! Mixed *ordinary* insertion convention and independent coefficient rule
on the common marker algebra (for RG02). The tag set may be disallowed
as a product. Two formal series BOTH carrying the same tag cannot be
multiplied and used as a single shared insertion; to compute the coefficient
of a tag representing a composite insertion, first multiply the ordinary
field factors and attach that tag once. This file also gives estimates using
Poly.price, not the sup norm on all markers. No conditional denominators or
connected subtractions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Tags
open Series Lattice Wilson Labels Source Function Set PowerSeries
open Marker Extra.Trajectories Wil
open scoped BigOperators Classical ContDiff Topology
variable {V I : Type*} [DecidableEq V] (R:Census V)

def wear (x : R.Mode) (p : PowerSeries ℂ) : PowerSeries (Poly R) :=
  PowerSeries.C (Poly.send x 1) * PowerSeries.map (Poly.bead R) p
lemma bead_at (x:R.Mode)(c:ℂ): Poly.send x 1 * Poly.bead R c=Poly.send x c:=
  (mul_comm ..).trans ((Poly.product_bead ..).trans (Poly.ext fun i=> by simp [mul_ite]))
lemma wear_at (x:R.Mode)(p:PowerSeries ℂ)(n:ℕ) :
    coeff n (wear R x p)= Poly.send x (coeff n p):=by simp only [wear,coeff_C_mul,coeff_map,bead_at]

def shared (x:R.Mode)(p q: PowerSeries ℂ) := wear R x (p*q)
lemma shared_at (x:R.Mode)(p q: PowerSeries ℂ)(n:ℕ) :
    (coeff n (shared R x p q)).part x =
      ∑ i∈Finset.range (n+1), coeff i p * coeff (n-i) q := by
  rw [shared,wear_at, Poly.part_send,if_pos rfl,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> coeff i p*coeff j q)]

def occurrences (tag:I→R.Mode)(f:I→ PowerSeries ℂ)(s:Finset I):=∏ i∈s,wear R (tag i) (f i)
lemma separate (tag:I→R.Mode)(f:I→ PowerSeries ℂ)(s:Finset I) (hf:Fits tag s):
    occurrences R tag f s = wear R (unionTag tag s hf) (∏ i∈s,f i):=by
  simp only [occurrences,wear,Finset.prod_mul_distrib,←map_prod]
  rw [tagged_prod tag s hf,Finset.prod_const_one]
lemma clash (tag:I→R.Mode)(f:I→ PowerSeries ℂ)(s:Finset I)(hf:¬ Fits tag s) : occurrences R tag f s=0:=by
  simp only [occurrences,wear,Finset.prod_mul_distrib,←map_prod]
  rw [show (∏ i∈s,Poly.send (tag i) 1)=0 from by contrapose! hf; exact fits_of_tagged_prod tag hf, map_zero,zero_mul]
lemma repeated (x:R.Mode)(p q:PowerSeries ℂ) (he:x≠R.quiet): wear R x p * wear R x q=0:=by
  unfold wear; rw [mul_mul_mul_comm,← map_mul]
  rw [show Poly.send x 1 * Poly.send x 1=0 from by
    by_contra hv; obtain ⟨i,hi,-⟩:=merges_of_tagged_mul hv
    apply he
    exact Subtype.ext (disjoint_self.mp hi), map_zero,zero_mul]

lemma toll (w:V→ℝ)(hw:∀ i,0<w i)(tag:I→R.Mode)(f:I→PowerSeries ℂ)(s:Finset I)(n:ℕ):
    Poly.price w (coeff n (occurrences R tag f s)) ≤ (∏ i∈s, Poly.toll w (tag i)) * ‖coeff n (∏ i∈s,f i)‖:=by
  classical
  by_cases hf:Fits tag s
  · rw [separate R tag f s hf,wear_at,Poly.solo,toll_union]
  rw [clash R tag f s hf,map_zero,Poly.zero_price]
  exact mul_nonneg (Finset.prod_nonneg (fun i _=> (Poly.worth hw _).le)) (norm_nonneg _)

lemma ps_product (f:I→ℝ→ℂ)(s:Finset I)(he:∀ i∈s,ContDiffAt ℝ ∞ (f i) 0):
    ContDiffAt ℝ ∞ (∏ i∈s, f i) 0 ∧ ps (∏ i∈s,f i)=∏i∈s,ps (f i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact ⟨contDiffAt_const, ps_one⟩
  | insert a s ha ih=>
    obtain ⟨hr,hp⟩:=ih (fun i hi=> he i (Finset.mem_insert_of_mem hi))
    have hu:=he a (Finset.mem_insert_self ..)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨hu.mul hr,(ps_mul _ _ hu hr).trans (by rw [hp])⟩

variable {G:Gauge} (F:Frames G) (S:(d:ℕ)→SectionData (F.level d)) (h:I→ℕ)(i:(j:I)→(F.level (h j)).Index) (A:I→Links ℤ G.Color) (tag:I→R.Mode)

def numerator (s:Finset I)(t:ℝ):=∏ j∈s,Poly.send (tag j) ((S (h j)).evaluate (Pi.single (i j) 1) (positive (A j) t))
def bareSeries := occurrences R tag (fun j=>book (S (h j)) (Pi.single (i j) 1) (A j))

/-- Exact ordinary Taylor/multiple-insertion compiler at the germ with real
expansion parameter and no partition factors.
-/
lemma compile (s:Finset I)(x:R.Mode)(n:ℕ):
    ordinary n (fun t=> (numerator R F S h i A tag s t).part x)=
      (coeff n (bareSeries R F S h i A tag s)).part x:=by
  let f (j:I)(t:ℝ):=(S (h j)).evaluate (Pi.single (i j) 1) (positive (A j) t)
  let b(j:I):=book (S (h j)) (Pi.single (i j) 1) (A j)
  have hf (j:I): ContDiffAt ℝ ∞ (f j) 0:=by
    unfold f; simp_rw [echo_exact]; exact ((echo_smooth (S (h j)) (Pi.single (i j) 1)).comp (g:=echo (S (h j)) _) (f:=fun t:ℝ=>t • restrictLog _ _) (contDiff_id.smul contDiff_const)).contDiffAt.of_le le_top
  change ordinary n (fun t=> (∏ j∈s,Poly.send (tag j) (f j t)).part x)= (coeff n (occurrences R tag b s)).part x
  by_cases he:Fits tag s
  · simp_rw [tagged_prod tag s he,Poly.part_send,separate R tag b s he,wear_at,Poly.part_send]
    split
    · rw [funext (fun t=> (Finset.prod_apply t s f).symm),←ps_at,(ps_product f s (fun j _=>hf j)).2]
      simp_rw [f,echo_book]; rfl
    exact (ordinary_const 0 _).trans (ite_self ..)
  rw [clash R tag b s he,map_zero,Poly.part_nil,show (fun t:ℝ=> _) = (fun _:ℝ=> (0:ℂ)) from ?hv]
  case hv=>
    funext t
    rw [show ∏ j∈s,Poly.send (tag j) (f j t)=0 from by contrapose! he; exact fits_of_tagged_prod _ he]; rfl
  exact (ordinary_const 0 _).trans (ite_self ..)

/-- Remove explicit bare link factors `g^l` in a whole distinct-occurrence
product before any RG evolutions. -/
def dressed (s : Finset I):=occurrences R tag (fun j=>letter (S (h j)) (i j) (A j)) s
lemma undress (pp:∀ d,Bid.pop (S d))(s:Finset I) :
    dressed R F S h i A tag s * PowerSeries.X^(∑ j∈s,((F.level (h j)).grades (i j)).2)=bareSeries R F S h i A tag s:=by
  let v j := ((F.level (h j)).grades (i j)).2
  have hu (x) (p q : PowerSeries ℂ): wear R x (p*q)=wear R x p * PowerSeries.map (Poly.bead R) q:=by simp [wear,mul_assoc]
  unfold bareSeries occurrences
  simp_rw [← powered_letter _ (pp _) ,hu,map_pow,PowerSeries.map_X,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl
lemma dressed_at (pp:∀ d,Bid.pop (S d))(s:Finset I)(x:R.Mode)(n:ℕ):
    (coeff n (dressed R F S h i A tag s)).part x=ordinary (n+∑ j∈s,((F.level (h j)).grades (i j)).2) (fun t=> (numerator R F S h i A tag s t).part x):=by rw [compile,←undress _ _ _ _ _ _ _ pp, PowerSeries.coeff_mul_X_pow]
end YM.Dict06.Tags
