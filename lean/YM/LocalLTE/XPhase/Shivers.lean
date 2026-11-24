import YM.LocalLTE.XPhase.Store
import YM.LocalLTE.XPhase.Part
/-!
# Preserving linear/mixed stencils after tally
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPhase
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open MergeProof Accent GridApprox.Nil Extra.Trajectories Extra.Multi Planned.GuardedAtom Guard Overlay
open PhysicalNext.Repeat
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
variable {w: V→ℝ} {t d s g e v y:ℝ} {N:ℕ}
variable [Fintype V] (B:Census V)(R:Rep G n)
-- mixed alphabet mark support. Keep zero padding possibly at fire. check presence for any NONZERO.
variable (A:Bands B R)
def Mob: Bands B R:={A with
   H:=fun j=> if 2≤ (A.rays j).val.card then A.H j else 0}
omit [Fintype V] in
lemma staff (h:A.Active): (Mob B R A).Active ∧ (∀ i,(Mob B R A).H i≠0 → 2 ≤ ((Mob B R A).rays i).val.card):=by
    refine ⟨⟨h.proper,h.pins,fun i=>?_,h.occurs,h.retained,h.inspects,h.keeps,h.meas,h.invi⟩,fun i hp=>?_⟩
    · unfold Mob; dsimp only; split
      next he=> exact h.regular _
      next=> exact Progress.DirectedRecipe.unspent R.p _ -- namespace?
    unfold Mob at hp; dsimp only at hp; split at hp; next he=> exact he
    next=> exact (hp rfl).elim
omit [Fintype V] in
lemma rateU (h:A.Radial w t d s g): (Mob B R A).Radial w t d s g:=by
    refine ⟨h.pure,h.localU,h.factor,?_,h.hits⟩
    obtain ⟨b,hb,h⟩:= h.bulk; refine ⟨b,fun i=>⟨(hb i).1, fun v hv=>?_⟩,h⟩
    unfold Mob; dsimp only; split; exact (hb i).2 v hv; exact Push.Local.bound_weaken (Progress.DirectedRecipe.no_cost R.p _ _) (hb i).1
lemma recollect (h:A.Active)(hq:A.Radial w t d s g)(hp:A.units=0)(U:Config G n) : (Mob B R A).extra U=Accent.octave (A.extra U):=by
   let f:= Mob B R A; have hv i : f.ray i U=Accent.octave (A.ray i U):=by
       unfold f Mob Overlay.Bands.ray; dsimp only; split
       next hh=>
         ext j; by_cases ht:j=A.rays i
         · rw [ht, Accent.crest _ _ hh]
         rw [Poly.part_send, if_neg ht]; by_cases he:2≤ j.val.card; rw [Accent.crest _ _ he,Poly.part_send,if_neg ht]; rw [Accent.starlet _ _ (Nat.lt_of_not_ge he)]
       next hh=>
         have hz: ∀ k,(A.ray i U).part k≠0→k=A.rays i := by
            intro k hk; unfold Bands.ray at hk; rw [Poly.part_send] at hk; split at hk
            next h=> exact h
            next=> exact (hk rfl).elim
         have hg: masked R.p.threshold (A.support i) (0:Config G n→ℂ) U=0:=congr_fun (map_zero (Push.Local.maskLinear ..)) _
         rw [hg,Poly.send_zero]; ext p; rw [Poly.part_nil]; by_cases ht:2≤ p.val.card; rw [Accent.crest _ _ ht]; exact (not_not.mp (fun h=> hh ((hz _ h) ▸ ht))).symm
         exact (Accent.starlet _ _ (Nat.lt_of_not_ge ht)).symm
   have ha:= (staff _ _ _ h).1; have hh : f.units=0:= hp; unfold Bands.extra; rw [hp,show (Mob B R A|>.units)= _ from hh]; simp only [Pi.zero_apply,Poly.send_zero, Finset.sum_const_zero,zero_add]
   ext x; have hx:= hq; rw [Poly.share ((Bands.bulkBound f ha (rateU B R A hq) U).1)]; change _=_; by_cases he:2≤ x.val.card; rw [Accent.crest _ _ he, Poly.share ((A.bulkBound h hq U).1)]; exact tsum_congr fun i=> congr_arg (fun f:Poly B=>f.part x) (hv i)|>.trans (Accent.crest _ _ he)
   have he:= Nat.lt_of_not_ge he; simp_rw [Accent.starlet _ _ he]; exact (tsum_congr (fun i=> by rw [show (Mob B R A|>.ray i U)= _ from hv i,Accent.starlet _ _ he]) : _=∑' i:ℕ,(0:ℂ)).trans tsum_zero
omit [Fintype V] in
lemma cleanE {m:ℕ}(k: ℝ) (hp: Port.Shine B A N m k) : Port.Shine B (Mob B R A) N m k := by
    constructor; intro i h; unfold Mob at h; dsimp only at h; split at h; swap; · exact (h rfl).elim
    next he=> unfold Mob; dsimp only; rw [if_pos he]; exact hp.legacy i h -- check
-- layout exact additional operator.FNormal. preserves.Mirror.
end YM.LocalLTE.XPhase
