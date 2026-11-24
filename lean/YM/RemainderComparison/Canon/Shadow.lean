import YM.RemainderComparison.Ethereal.Product

/-!
# Common represented Push at null markers
No exponent of per-site budgets (can use as Π=0 pre-β comparison).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Canon
open Function Filter Finset Lattice Wilson RG Pressure -- edit
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open WickReps PhysicalNext.Repeat Lotus Merge Palette Turn Mosaic Marker Serif Lacuna Ethereal
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{ι I : Type}{n f:Side}{S:StepData n f}{α:Type*}{β:Type}[DecidableEq β]
variable (P' : Vowel G n ℕ)(H:Flues.Yard ι α G n)
variable (J: Marker.Census β)(A:Set ι)(u : ι→ℝ)(bℓ:α) (b:ℝ)(t:Tree.Forest S.ratio)

section input
variable {R:Rep G f}(M:ι→Lotus.Leaf R)
lemma emptyWeight (p:Lyric.Drums M S)(h:p.val=∅) (U: Config G f): (team M p).cicada U=R.eval U:=by
    have ht : (team M p).own=∅:=by unfold team; dsimp only; rw [h]; simp
    have hh : (team M p).gasDue=∅:=by unfold Team.gasDue; rw [ht]; simp; rfl
    unfold Team.cicada Rep.eval Activities.gas; apply congr_arg; refine tsum_congr fun j=>?_ ; unfold Team.bun Activities.gasOccurrence; split; next=>
      unfold Team.bill Team.ingredients; rw [ht,hh]; simp
    rfl
lemma null (U:Config G f): Serif.TuneR M (Set.univ) u b (fun _=> (0: Poly J)) S U=tint J (R.eval U):=by
    let i := Tickets.none (Palette.sign M S); unfold Serif.TuneR; rw [tsum_eq_single i]
    · unfold Verse.paint; rw [Flues.cold (Set.univ) (fun _=> (0:Poly J)) _ (show Verse.load Set.univ (raw M i).letters=0 from by unfold Verse.load; rw [show (raw M i).letters=0 from rfl]; simp)]; unfold Lacuna.tint; congr 2
      rw [Verse.emit,Verse.stock,show (raw M i).letters=0 from rfl]; simp only [Multiset.map_zero,Multiset.prod_zero,one_mul]; exact emptyWeight M i rfl _
    intro j hj; unfold Verse.paint; rw [Lacuna.paintless J Set.univ ..,smul_zero]
    intro ht; apply hj; apply Subtype.ext; change j.val=∅; apply Finset.card_eq_zero.mp; unfold Verse.load raw at ht; simpa only [Set.mem_univ,Multiset.filter_true] using! ht
end input
variable {V W:ℝ}
lemma paired (f:I→ℝ) (s:Finset I): ∏ i∈s,Lacuna.tint J (f i)= Lacuna.tint J (∏ i∈s,f i):=by
    unfold Lacuna.tint; rw [Finset.prod_smul, Finset.prod_const_one,Complex.ofReal_prod]

open Jolt Flues MeasureTheory
variable {I₁ I₂:Type}
variable (p:BudgetPoint)
local notation "Qv"=> Ethereal.manor P' H A bℓ
variable (hp: (Ethereal.manor P' H A bℓ).Valid p V W)
variable (U:Config G n)
include hp
lemma sheen : HasSum (H.gala p A (fun _=>(0:Poly J)) bℓ U) (tint J ((Qv).gas p U)):=by
   refine (Lacuna.tintSum J ((Activities.gasSeries hp).summable U|>.hasSum)).congr_fun fun i=>?_
   unfold Yard.gala Merge.Photo.fronts Activities.gasOccurrence; by_cases hi:(H.manifest bℓ).admissible p U i
   · rw [if_pos hi,if_pos (show (Qv).admissible p U i from hi), ← paired]
     refine Finset.prod_congr rfl fun j _=> ?_; by_cases hv:Jolt.phase H A j
     · unfold Yard.song; rw [show (Qv).K j=H.glow bℓ j from if_pos hv, Flues.cold A _ _ hv]; rfl -- check syntax
     unfold Yard.song; rw [Lacuna.paintless J A _ (show _≠0 from hv), smul_zero,show (Qv).K j=0 from if_neg hv]; unfold Lacuna.tint; simp
   rw [if_neg hi, if_neg (show ¬ (Qv).admissible p U i from hi)]; simp only [tint]; simp

open GridRenewal.Rain
variable (B:Manor G n ι α I₁)(T:Manor G n ι α I₂)
variable (E:Rep G n)(z:BudgetPoint)

lemma kernel (he:E.p=p)(hE:E.activities=Ethereal.manor P' H A bℓ):
    let z:ι→Poly J:=fun _=>0
    (Complex.ofReal (Real.exp (E.exponent U))) • (cyclone (Lacuna.day J A B p z bℓ U+Lacuna.day J A T p z bℓ U) * (∑' i,H.gala p A z bℓ U i))=tint J (E.eval U):=by
    dsimp only; rw [Lacuna.blankDay,Lacuna.blankDay,add_zero,show cyclone (0:Poly J)=1 from ?_,show (∑' i,H.gala p A (fun _=> (0:Poly J)) bℓ U i)= _ from (sheen P' H J A bℓ p hp U).tsum_eq]
    · rw [one_mul,tint,tint,← mul_smul,RG.Rep.eval, hE, he, Complex.ofReal_mul]
    convert! (Flues.evaporate (p:=(0 : Marker.Poly J)) (by simp)) using 1; simp
omit hp
-- scalar push.S.EVAL all U.unmixed. Auxiliary physical role with e_natural coe
lemma basin {G:Gauge}{c f:Side}(S:StepData c f)(β':ℝ)(l:Config G f→ℝ)(V:Config G c) : S.push β' (fun U=> Lacuna.tint J (l U)) V=Lacuna.tint J (S.push β' l V):=by
    unfold RG.StepData.push; change (∫ x,S.density β' x V • (l x • (1:Poly J)) ∂Wilson.prior G f)=(∫ x,S.density β' x V * l x ∂Wilson.prior G f) • (1:Poly J); rw [← integral_smul_const]; exact integral_congr_ae (ae_of_all _ fun _=> (mul_smul ..).symm)
variable {ν:Rep G f}(z:ι→Leaf ν)(u:ι→ℝ)
include hp
-- If all real Rendering input extra unmarked vacuum perturbations are already in invoking rep, use comparison as canonical History there. Otherwise supplies predicate A Vera.
lemma reper {b:ℝ} (he:E.p=p)(hE:E.activities=Ethereal.manor P' H Set.univ bℓ)(S : StepData n f)
    (hX: Set.univ=A) -- reserved
    (h:S.push ν.beta (Serif.TuneR z (Set.univ) u b (fun _=> (0: Poly J)) S) U=Complex.ofReal (Real.exp (E.exponent U)) •
       (GridRenewal.Rain.cyclone (Lacuna.day J A B p (fun _=>0) bℓ U+Lacuna.day J A T p (fun _=>0) bℓ U)*(∑' i,H.gala p A (fun _=> (0:Poly J)) bℓ U i))): S.push ν.beta ν.eval U= E.eval U:=by
    rw [hX] at hE
    rw [show TuneR z Set.univ u b (fun _=>0) S=(fun x=> Lacuna.tint J (ν.eval x)) from funext (Canon.null J u b z), Canon.basin] at h
    exact Lacuna.color _ (h.trans (Canon.kernel P' H J A bℓ p hp U B T E he hE)) -- arguments after inspect
end YM.RemainderComparison.Canon
