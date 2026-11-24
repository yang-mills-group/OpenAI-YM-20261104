import YM.FormalOPE.RG10.Join.Recruits

/-! Price where actually joined, not with multiplicity for all absent partner terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Joins
open MeasureTheory PowerSeries Finset Marker Extra.Trajectories FlatFeed Word Polar Function
open Primitives.GCC Primitives.GCC.Anchor
open YM.Multi (parts shards unionOf)
open scoped BigOperators Topology Classical
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E) (W : Vertices (Θ × E))
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {R : Census V} {S : Census I} (P : Subalgebra ℂ (Θ × E → ℂ)) (hP : accepts F P)

lemma disassemble (q : R.Mode) {J : V → Type*} (t : (x : V) → Finset (J x))
    (f : ∀ i : V, J i → P) : tally F q (fun i => (∑ j∈t i,f i j : P).val) =
    ∑ i∈Fintype.piFinset (fun x : ↥q.val => t x.val), (award F P hP q) fun j:↥q.val=> f j.val (i j) := by
  rw [award_eq F P hP q (fun i => ∑ j∈t i,f i j)]
  exact (award F P hP q).map_sum_finset ..


abbrev Payload (I : Type) [Fintype I] [DecidableEq I] (R : Census V) := YM.Multi.Hot (budget R I)

variable {J : Payload I R → Type*} (t : ∀ k, Finset (J k))
local notation "T" => Polar.budget R I
variable (A : Θ × E→ Word R) (f : ∀ p, J p → P)

def actor (p : Payload I R) := ((∑ j∈t p, f p j : P).val)

theorem linked (hp : Performs W I A (actor P t f)) (hv : Word.read R.quiet A=1)
    (s : R.Mode) (hs : s.val.Nonempty) (k : Finset I) :
    (k.card.factorial:ℂ) * (PowerSeries.coeff k.card (see s (F.contraction W A))) =
    ∑ i∈shards T (pay s k), ∑ e∈Fintype.piFinset (fun x:↥i.val => t x.val),
      (award F P hP i) fun j => f j.val (e j) := by
  rw [chargeFormula F W A hv s hs k _ hp (partners_account F P hP (fun i => ∑ j∈t i, f i j))];
  exact sum_congr rfl fun i _ => disassemble F P hP i t f -- check

def chosen (q : (parts T).Mode) (e : ∀ x:↥q.val, J x.val) := lineup P q (fun j => f j.val (e j))
lemma earned (q : (parts T).Mode) (e : ∀ x:↥q.val, J x.val) : tally F q (chosen P f q e) =
    (award F P hP q) (fun j => f j.val (e j)) := rfl

lemma nonempty_marker {s : R.Mode} (hs : s.val.Nonempty) {k : Finset I}
    (i : (parts T).Mode) (h : i∈shards T (pay s k)) : i.val.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr; intro he
  have hx : i=(parts T).quiet := Subtype.ext he
  have h := (mem_filter.mp h).2; rw [hx, YM.Multi.unionOf_empty, ← pay_quiet] at h
  exact hs.ne_empty (congr_arg Subtype.val ((pay_inj ..).1 h).1.symm)
end YM.FormalOPE.RG10.Joins
