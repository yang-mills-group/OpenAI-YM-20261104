import YM.Comparison.RG02.Order.Vacancy
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
/-!
# Restrict order or insertion horizon

Announce subsets only. Truncated coefficient comparison; no represented-cost bound. If merely
changing radii/root units without changing types use `Multi.dilation`, not `restriction` (scaling
adapter also derived below). When restricting insertions keep the actual supports and their masks,
including window indicator reads. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Finset Function YM.Marker YM.Multi Join YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories
open YM.Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V V' W W' : Type} [DecidableEq V] [DecidableEq V'] [DecidableEq W] [DecidableEq W']
    [Fintype V] [Fintype V'] [Fintype W] [Fintype W']
    {R : Census V} {R' : Census V'} {S : Census W} {S' : Census W'}
    {r r' : ℕ}

namespace Join
private lemma image_pair (u : Names R R') (v : Names S S') (a : R.Mode) (b : S.Mode) :
    (pair a b).val.image (u.e.sumMap v.e)=(pair (u.share a) (v.share b)).val := by
  ext (i|j)
  all_goals simp [pair,Names.share]

def sub (u : Names R R') (v : Names S S') : Names (room R S) (room R' S') where
  e := u.e.sumMap v.e
  visible s := by rw [← pair_reunite s,image_pair]; exact (pair ..).property

lemma sub_pair (u : Names R R') (v : Names S S') (a : R.Mode) (b : S.Mode) :
    (sub u v).share (pair a b)=pair (u.share a) (v.share b) := Subtype.ext (image_pair u v a b)
end Join

omit [Fintype V] [Fintype V'] in
lemma part_restrict (u : Names R R') (x : Poly R') (s : R.Mode) :
    (u.restriction x).part s=x.part (u.share s) := rfl

-- allow arbitrary injection of coupling markers, not just casts.
def indexNames (h : Fin r ↪ Fin r') : Names (indices r) (indices r') := ⟨h,fun _=> mem_univ _⟩
def truncate (u : Names R R') (h : Fin r ↪ Fin r') := (Join.sub u (indexNames h)).restriction
lemma trunc_part (u : Names R R') (h : Fin r ↪ Fin r') (x : Grade R' r') (t : R.Mode) (s : Index r) :
    (truncate u h x).part (Join.pair t s)=x.part (Join.pair (u.share t) ((indexNames h).share s)) := by
  unfold truncate; rw [part_restrict,sub_pair]
lemma trunc_quiet (u : Names R R') (h : Fin r ↪ Fin r') (x : Grade R' r') :
    (truncate u h x).part (Board R r).quiet=x.part (Board R' r').quiet := by rw [← pair_quiet,trunc_part]; simp
lemma trunc_series (u : Names R R') (h : Fin r ↪ Fin r') (x : PTable R') :
    truncate u h (series R' r' x)=series R r (PowerSeries.map u.restriction x) := by
  have ht s : ((indexNames h).share s).val.card=s.val.card := Finset.card_image_of_injective _ ( (indexNames h).e).injective
  apply both_parts; intro t s; rw [trunc_part, polarization, ht, polarization,PowerSeries.coeff_map,part_restrict]
lemma trunc_log (u : Names R R') (h : Fin r ↪ Fin r') {x : Grade R' r'} (hx : UnitLeading x) :
    truncate u h (connected x)=connected (truncate u h x) := (Join.sub u (indexNames h)).connected_restrict hx
lemma trunc_bottom (u : Names R R') (h : Fin r ↪ Fin r') (x : Grade R' r') :
    truncate u h (bottom R' r' x)=bottom R r (truncate u h x) := by
  apply both_parts; intro t s; rw [trunc_part,bottom_value,bottom_value,trunc_part,u.quiet]
  by_cases he:t=R.quiet; subst t; simp
  simp only [he,↓reduceIte]; rw [if_neg (fun e => he (u.inj (e.trans u.quiet.symm)))]
lemma trunc_inverse (u : Names R R') (h : Fin r ↪ Fin r') {x : Grade R' r'} (hx : UnitLeading x) :
    truncate u h (inverseMass x)=inverseMass (truncate u h x) := by
  unfold inverseMass; rw [show truncate u h (Poly.pass (-connected x))=_ from (Join.sub u (indexNames h)).pass_restrict (by rw [Poly.part_neg,connected_quiet hx,neg_zero])]; rw [← trunc_log u h hx]; rfl
lemma trunc_ratio (u : Names R R') (h : Fin r ↪ Fin r') {x : Grade R' r'} (hx : UnitLeading x) :
    truncate u h (ratio x)=ratio (truncate u h x) := by unfold ratio denominator; rw [map_mul, trunc_inverse u h ((bottom_quiet _).trans hx),trunc_bottom]
lemma trunc_sym (u : Names R R') (h : Fin r ↪ Fin r') {x : Grade R' r'} (hx : Symmetric x) :
    Symmetric (truncate u h x) := by obtain ⟨p,rfl⟩:=hx; rw [trunc_series]; exact Symmetric.known _
lemma trunc_observe (u : Names R R') (h : Fin r ↪ Fin r') {x : Grade R' r'} (hx : Symmetric x) {n : ℕ} (he : n≤r) :
    u.restriction (observe _ _ x n)=observe _ _ (truncate u h x) n := by
  obtain ⟨p,rfl⟩:=hx; rw [trunc_series,observation _ _ _ he,observation _ _ _,PowerSeries.coeff_map]
  exact he.trans (by simpa using Fintype.card_le_of_embedding h)

-- marker scales (field recalibration or extra derivative/source radius shifts)
def reweight (a : V→ℂ) : Grade R r→ₐ[ℂ] Grade R r := dilation (Board R r) (Sum.elim a 1)
lemma reweight_part (a : V→ℂ) (x : Grade R r) (s : R.Mode) (t : Index r) :
    (reweight a x).part (Join.pair s t)=(∏ i∈s.val,a i)*x.part (Join.pair s t) := by
  rw [reweight,dilation_part];
  change (∏ i∈ s.val.disjSum t.val, _)* _=_; rw [prod_sumElim]; simp
lemma reweight_series (p : PTable R) (a : V→ℂ) :
    reweight a (series R r p)=series R r (PowerSeries.map (dilation R a).toRingHom p) := by
  apply both_parts; intro t s; rw [reweight_part,polarization,polarization,PowerSeries.coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dilation_part]; ring
lemma reweight_denominator (x : Grade R r) (a : V→ℂ) : denominator (reweight a x)=denominator x := by
  apply both_parts; intro s t; simp only [denominator,bottom_value,reweight_part,Census.quiet,prod_empty,one_mul]
end YM.Comparison.RG02.Order
