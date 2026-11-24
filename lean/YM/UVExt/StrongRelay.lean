import YM.UVExt.MixedTrials
import YM.MergeProof.Chaletbin
import YM.MergeProof.Eureka
import YM.MergeProof.Powder

/-!
# Keeping a microscopic, not just single-slot-exact, bin witness

This strengthens the *production* used to obtain extraction groups, not an inference
from just `Spec.CLOSED`. It will permit erasure even amongst several shifted/differenced
local insertions at once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Slots
open Set Function MeasureTheory Filter Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels Maxwell
open YM.MergeProof
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G : Gauge} {C : Family G} {d : ℕ} {A : Table C.book} {R : Dash.Bin A} {o : Extraction.Order}

def manifest (Z : Trial C) := ∃ r m : ℕ, ∀ N p:ℕ, ∃ f : Mark.Pre G, Continuous f ∧ Mark.MicroAt f r m ∧
    ∀ (x:Site (C.side N p)) (U:Config G (C.side N p)), Z N p x U = f (expandAt x U)

structure StrongBin (C : Family G) {S : Table C.book} (R : Dash.Bin S) (F : Extraction.Order) (d : ℕ) : Prop where
  mark (x : Rowe C d) : (∀ j,(R d).step j (x j)=0) → dollar C F x →
    ∃ z, manifest (C:=C) z ∧ Stencilled F z ∧ Bid.close C F (Bid.upper C x-z)
  -- One cap for each mixed derivative localized in one slot, paying its own weight
  vets (x : C.label d) (p : List Axis) : vet C F (d+p.length) (slotField (C:=C) ⟨d,x⟩ p)

section Mark
variable {δ : ℕ} {F : Frame G d} {H : Hol G}
private lemma micro_sum (I : Finset (Fin δ)) (f : Fin δ → Mark.Pre G) {r m : ℕ} (hf : ∀ i∈I,Continuous (f i))
    (h : ∀ i∈I,Mark.MicroAt (f i) r m) : Mark.MicroAt (∑ i∈I,f i) r m := by
  induction I using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Mark.MicroAt.zero G r m
  | insert i s hi ih=>
    rw [Finset.sum_insert hi]
    let a := Finset.mem_insert_self i s
    have he : Continuous (∑ j∈s,f j) := by
      rw [funext (fun x : CoverConfig G=> Finset.sum_apply x s f)]
      exact continuous_finsetSum _ fun j hj=> hf j (Finset.mem_insert_of_mem hj)
    apply (h i a).add _ (hf i a) he
    exact ih (fun i hi=>hf i (Finset.mem_insert_of_mem hi)) (fun i hi=>h i (Finset.mem_insert_of_mem hi))

theorem uniform_micro (W : Mark.Weave G) (X : SectionData F) (he : Mark.Portfolio H X (W d)) :
    ∃ r m : ℕ,∀ x : Label G d,x∈Maxwell.equationIdeal G d → Mark.MicroAt (X.evaluate (F.coords (W d x))) r m := by
  let S := Maxwell.equationIdeal G d
  have hp {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (P : Submodule ℂ V) :
      Module.Free ℂ P ∧ Module.Finite ℂ P := ⟨inferInstance,inferInstance⟩
  haveI := (hp S).1; haveI := (hp S).2
  let E := Module.finBasis ℂ S
  let f : S →ₗ[ℂ] Mark.Pre G := ((X.eval_linear).mk' X.evaluate).comp
    (F.coords.toLinearMap.comp ((W d).toLinearMap.comp S.subtype))
  choose r m h using fun i=> (he.rank (E i).1 (E i).2).2
  let M := Finset.univ.sup m
  let A := Finset.univ.sup r
  refine ⟨A,M,fun x hx=>?_⟩
  let z : S := ⟨x,hx⟩
  change Mark.MicroAt (f z) _ _
  rw [← E.sum_repr z,map_sum]; simp_rw [map_smul]
  refine micro_sum _ _ ?_ ?_
  · intro i _; apply Continuous.const_smul; exact (he.rank (E i).1 (E i).2).1
  intro i hi; exact ((h i).mono (Finset.le_sup (s:=Finset.univ) (f:=r) hi) (Finset.le_sup (s:=Finset.univ) (f:=m) hi)).scale (E.repr z i)
end Mark
section Merge
variable (H:C.Makes)(B:Stock.Tabs C.path.levels)
variable {f:Extraction.Order}{N p d:ℕ}(V:SectionData (C.labels.level d)) (R : Mark.Weave G)
    (hV: Mark.Portfolio C.params V (R d)) {ζ:ℕ→ℕ→ℝ}{E:ℕ→ℝ}(P:ℕ→ℕ→(C.label d≃ₗ[ℂ] C.label d)){U:ℕ→ℕ→(C.labels.level d).Index→ C.label d}
    (h:Hearth V ζ E P U)
local notation "F"=> C.labels.level d
local notation "Z"=> (C.factory d N p).terminal
open Mark (Weave theta Active Portfolio)
include hV
lemma hallmark_micro (b : Rowe C d) (hx : ∀ j : Cutoffs, (C.factory d j.1 j.2).terminal (b j) ∈ Mark.carrier C R d j.1 j.2) :
    manifest (hallmarks V b) := by
   obtain ⟨s,H,hH⟩ := uniform_micro R V hV
   refine ⟨s,H,fun N p=>?_⟩
   let X := C.factory d N p; obtain ⟨y,hy',h0⟩:= Mark.obtained R _ (hx (N,p))
   have hz (i : Site (C.side N p)) : hallmarks V b N p i=((C.S.a N:ℂ)^d)⁻¹ • (V.evaluate ((C.labels.level d).coords (R d y)) ∘ expandAt i):=by
      unfold hallmarks; unfold Mark.embedTo at h0; simp only [LinearEquiv.trans_apply] at h0; unfold initial; rw [(C.factory d N p).terminal.injective h0]
      let j:= C.path.levels.clock.threshold N; rw [show ∀ w:C.label d,(C.labels.level d).scaled j⁻¹ (Mark.tied C d N w)=w from (Mark.tied C d N).left_inv]; rfl
   exact ⟨_,(V.continuous_evaluate _).const_smul (((C.S.a N:ℂ)^d)⁻¹),((hH y hy').scale (((C.S.a N:ℂ)^d)⁻¹)),fun i x=> congr_fun (hz i) x⟩
include h B H
set_option maxHeartbeats 200000 in
lemma marshal_strong (x:Rowe C d) (hv:dollar C f x) (hp:∀ j,x j∈ catalog C R d j.1 j.2 (P j.1 j.2)) :
    ∃ z,manifest z ∧ Stencilled f z ∧ Bid.close C f (upper C x-z):= by
   let Z'(i : Cutoffs):= (C.factory d i.1 i.2).terminal; let y:Rowe C d := fun i=> (P i.1 i.2).symm ((Z' i).symm (x i))
   have he(i) : Z' i (P i.1 i.2 (y i))=x i:=by unfold y; rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
   have hx(i): Z' i (y i) ∈ Mark.carrier C R d i.1 i.2:=by
      obtain ⟨v,hv,hw⟩:= hp i; change bindP C R d i.1 i.2 _ v = x i at hw; unfold Z' y; rw [← hw,bindP,Astar,LinearEquiv.trans_apply,LinearEquiv.trans_apply, LinearEquiv.trans_apply]; simp only [Z', LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]; exact Mark.entry_mem C R d i.1 i.2 _ hv
   have hc:= (dollar_slow _).1 hv
   have hy : Slow C f y:=by
     apply ((Slow.const (C:=C) (f:=f) (2:ℝ)).mul (coords_slow _ hc)).reduce
     filter_upwards [(cutoff_grows f).eventually h.stamped] with i hi; exact ((Size.norm_le _ _).trans ((hi i.2).2.1 ((Z' i).symm (x i)))).trans (Real.le_norm_self _)
   refine ⟨hallmarks V y,hallmark_micro V R hV y hx,region V hV.valid y,?_⟩
   have hV:= embark H B V hV.valid h y hy; change Bid.close C f (upper C _-hallmarks V y) at hV; change Bid.close C f (upper C (fun i=>Z' i (P i.1 i.2 (y i)))-hallmarks V y) at hV; rw [show (fun i:Cutoffs=>Z' i (P i.1 i.2 (y i)))=x from funext he] at hV; exact hV
end Merge
section Produce
variable (H:C.Makes)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D)(hF:Fridge C u ζ){f:Extraction.Order} {N p d:ℕ} (V:∀ d:ℕ,SectionData (C.labels.level d))(R:Mark.Weave G)(hV:∀ d, Mark.Portfolio C.params (V d) (R d))(hG:G.Simple)
set_option quotPrecheck false
include h hV H hG hF B
lemma strong_produce (hb:∀ d:ℕ,∃ a: ℕ→ℝ,Braze (C:=C) (V d) a): ∃ P b, Scotia C R P b ∧ (∀ (T : Table C.book) (L : Dash.Bin T) (f:Extraction.Order) (a : ∀ d:ℕ,ℕ → CoordMap C d), Projected b f L a → ∀ d:ℕ,StrongBin C L f d):=by
    choose P hp using hb; choose E Y U hY using fun d=> solaris H B h hF (V d) (hV d).valid hG (hp d)
    choose M hm hM using fun d:ℕ=> Mark.potage (C.labels.level d); choose F hK hQ hs using fun d:ℕ=> fun i:Cutoffs => hM d (catalog C R d i.1 i.2 (Y d i.1 i.2)); let b:Presentation C:=⟨F,fun d i=> (hK d i).stable⟩
    refine ⟨fun d i=> Y d i.1 i.2,b,⟨fun f=> ?_,fun d=>?_,fun d N p=>hK d (N,p), fun f d=>?_⟩,?_⟩
    · exact ⟨fun d p=>⟨_,(hm d).le,Eventually.of_forall fun j=> hQ d (f.mesh j,p)⟩, fun d=>⟨_,(hm d).le, Eventually.of_forall fun p=> Eventually.of_forall fun j=> hQ d (f.mesh j,f.per p)⟩⟩
    · filter_upwards [catalog_symm H (V d) R (hV d) _ (hY d)] with i hi p; obtain ⟨hv,hh⟩:=hi p; refine ⟨hv,hh,hs d (i,p) ?_⟩; let L:= bindP C R d i p (Y d i p); constructor
      · intro s x h; obtain ⟨w,hw,hW⟩:=h; subst x; exact ⟨_,Mark.turn_ideal s hw,hh w s⟩
      intro x hx; obtain ⟨w,hw,hW⟩:=hx; subst x; exact ⟨_,Mark.conjugate_ideal hw,hv w⟩
    · refine ⟨fun x hx hv=> marshal H B (V d) R (hV _) _ (hY d) _ hv (fun j=> ((hK d j).ker) ▸ (show x j∈LinearMap.ker (F d j).toLinearMap from LinearMap.mem_ker.mpr (hx j))),fun w hw x=> thyme H B h hG hF x d hw,fun x a=> lofty H B h hG hF x a⟩
    · intro T L f a ha d; refine ⟨fun x hx hv=>marshal_strong H B (V d) R (hV d) _ (hY d) _ hv
       (fun j=> ((hK d j).ker) ▸ (show x j∈LinearMap.ker (F d j).toLinearMap from LinearMap.mem_ker.mpr ?_)),fun x p=>onions H B h hG hF _
           (protectedMixed H hG (hF.shifts f) _ _) (stencilled_mixed (Stencilled.visits H x) p)
           (Eventually.of_forall fun i=>slot_continuous _ _ _ _ _)⟩
      rw [show F d = b.step d from rfl,← ha.same d]; exact hx j
set_option quotPrecheck false
end Produce
end YM.UVExt.Slots
