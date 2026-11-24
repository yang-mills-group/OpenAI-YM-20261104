import YM.FormalOPE.RG10.Join.Output
import YM.Next.MULTISOURCE.Monomial

/-! # Partner contributions are genuine joint cumulants.

Use any representation verified on the **uncut germ** (usually as sums of localized/rooted
packets) in this connected decomposition. Works degree by degree, and without analytical or
existence loss from any estimate on the connected *output*. This is the bridge to summing even
tadpole/self contractions and log and Jacobian vertices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Joins
open MeasureTheory PowerSeries Finset Marker Extra.Trajectories FlatFeed Word Polar Function
open scoped BigOperators Topology Classical

variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E) (W : Vertices (Θ × E))
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {R : Census V} {S : Census I} {X : Type*}

/-- Canonical charge kernel (an ordinary function of the joint field, NOT l1 kernel norm).
Polarized component of **log integrand before expectation**. If supplying each from local Wilson
vertex/lift computations, give an equality at this `driver`. Also includes rank-zero marked
terms and vacuum log packets & Jacobians of positive degree. -/
def driver (I : Type) [DecidableEq I] [Fintype I] (A : Θ × E→Word R) :
    YM.Multi.Hot (budget R I) → Θ × E → ℂ := fun u x => (connected (present I (totalize W A x))).part u.val

open YM.Multi (Hot lambda lit substitute parts shards unionOf)

omit [Fintype V] in
private lemma all_present {x : Poly R} (h : x.part R.quiet=0) : lit R (fun u => x.part u.val)=x := by
  ext i; by_cases he : i.val.Nonempty
  · exact YM.Multi.part_lit _ ⟨i,he⟩
  rw [show i=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp he), YM.Multi.part_lit_quiet,h]

lemma commute_conn (M : Poly (parts R)) (hm : M.part (parts R).quiet=1) :
    connected (substitute R M) = substitute R (connected M) := by
  refine (PolyUtil.conn_map _ (fun x=> ?_) M hm).symm
  rw [YM.Multi.substituted, shards, sum_eq_single (parts R).quiet]
  · intro b hb hB; have hc : b.val.Nonempty:= nonempty_iff_ne_empty.mpr (fun hh => hB (Subtype.ext hh))
    have hw : (unionOf b).val.Nonempty := (YM.Multi.unionOfHot ⟨b,hc⟩).property
    rw [(mem_filter.mp hb).2] at hw; exact False.elim (hw.ne_empty rfl)
  simp

lemma exponential_components (a : V → ℂ) (q : R.Mode) : (Poly.pass (lambda R a)).part q =
    ∏ i∈q.val,a i := by
  unfold lambda; rw [Extra.Trajectories.pass_sum _ _ (by simp [Census.fire])]; exact YM.Multi.polynomial ..

/-- Keep the driver law as an explicitly exponential expression so a local proof can either
supply driver equality (often directly from vertices) or apply `performs_canonical`. -/
def Performs (I : Type) [Fintype I] [DecidableEq I]
    (A : Θ × E→Word R) (φ : YM.Multi.Hot (budget R I) → Θ × E→ℂ) :=
  ∀ x,present I (totalize W A x) = (lit (budget R I) (fun p => φ p x)).pass

omit [Fintype Θ] [MeasurableSpace E] in
lemma Performs.isDriver (A : Θ × E→Word R) (φ : YM.Multi.Hot (budget R I) → Θ × E→ℂ)
    (h : Performs W I A φ) : driver W I A = φ := by
  funext p x; unfold driver; rw [h, PolyUtil.conn_pass _ (YM.Multi.part_lit_quiet _)]; exact YM.Multi.part_lit ..

omit [Fintype Θ] [MeasurableSpace E] in
lemma performs_canonical (A : Θ × E→Word R) (h : Word.read R.quiet A=1) : Performs W I A (driver W I A) := by
  intro x; unfold driver
  rw [all_present (connected_quiet (unit_present W A h _)),pass_connected (unit_present W A h _)]

def guests (f : V → X → ℂ) (s : R.Mode) := ∏ i∈s.val,f i

def partners (R : Census V) (f : V → Θ × E→ℂ) : Poly R := Poly.inject fun s => F.mean (guests f s)
omit [Fintype V] in
lemma partners_one (R : Census V) (f : V → Θ × E→ℂ) : (partners F R f).part R.quiet=1 := F.mean_one

/-- Authenticate the integrability of partner statistics on every actually used subset (selection
census). -/
def accounted (R : Census V) (f : V → Θ×E→ℂ) := ∀ s : R.Mode,F.Pays (guests f s)

omit [Fintype Θ] [MeasurableSpace E] in
lemma performs_terms {A : Θ × E→Word R} (s : (budget R I).Mode) (x : Θ × E) {φ}
    (hp : Performs W I A φ) : (present I (totalize W A x)).part s =
    ∑ i∈shards (budget R I) s, guests φ i x := by
  rw [hp, ← YM.Multi.substitute_lambda (fun p => φ p x),
    ← YM.Multi.pass_map _ _ (YM.Multi.lambda_quiet _) (by rw [YM.Multi.substitute_lambda, YM.Multi.part_lit_quiet]),
    YM.Multi.substituted]
  exact sum_congr rfl fun i _ => (exponential_components ..).trans (Finset.prod_apply ..).symm

lemma represents {A : Θ × E→Word R} {φ} (hp : Performs W I A φ)
    (ha : accounted F (parts (budget R I)) φ) : present I (F.columns (totalize W A)) =
      substitute (budget R I) (partners F (parts (budget R I)) φ) := by
  ext q; rw [measurement, YM.Multi.substituted]
  let f := guests (R:=parts (budget R I)) φ
  rw [show (fun x => (present I (totalize W A x)).part q) = ∑ i∈ shards (budget R I) q,f i from
    funext (fun x => (performs_terms W q x hp).trans (Finset.sum_apply ..).symm), mean_sum _ _ (fun i _ => ha i)]; rfl

theorem chargeFormula (A : Θ × E→Word R) (h : read R.quiet A=1)
    (s : R.Mode) (hs : s.val.Nonempty) (k : Finset I)
    (φ : YM.Multi.Hot (budget R I) → Θ × E → ℂ) (hp : Performs W I A φ)
    (ha : accounted F (parts (budget R I)) φ) :
    (k.card.factorial:ℂ) * (PowerSeries.coeff k.card (see s (F.contraction W A))) =
    ∑ i∈shards (budget R I) (pay s k), (connected (partners F (parts (budget R I)) φ)).part i := by
  rw [disbursed F W A h s hs k, represents F W hp ha, commute_conn _ (partners_one F ..), YM.Multi.substituted]
end YM.FormalOPE.RG10.Joins
