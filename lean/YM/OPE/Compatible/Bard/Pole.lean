import YM.OPE.Compatible.Bard.Lumbar
/-!
# Bias combination with preloaded axes

Reports remain Stem, choose cap independently. Here supplying through
actual H, not the limiting readout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {V W I: Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype I][DecidableEq I]{G:Gauge}{C:Family G}
    {d N p k:ℕ}{A:Allot C} (X: Extra.Histories.Music (C.labels.level d) C.path N p){P:Ensemble V} {P':Ensemble W}
    {D:V ↪ W}{E:W→ Site (C.S.side k p)} {Y:Stem W G (C.S.side k p)}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "R"=> C.path.rep N p
local notation "B"=> R k
local notation "α"=> alto C.path k d
local notation "V!"=> (F).Index
local notation "D!"=> C.factory d N p
open Deb Relay
variable {y:Coefficient (C.labels.level d) (C.side k p)}{η x q w:ℝ}
-- ded alignment for old
omit [DecidableEq V][Fintype V][Fintype W][DecidableEq W] in
lemma Stamp_back (h:Screenlet P P' D)(he:Marked (R k) E P' Y)(hp:Stamp (N:=N) P (C.localSection d) (E ∘ D) y (cropStem D Y)): Stamp (N:=N) P' T E y Y:=by
   refine ⟨he,?_,?_⟩
   · rw [← h.start]; exact hp.real'
   rw [← h.start]; exact hp.price
omit [DecidableEq V][Fintype V][Fintype W][DecidableEq W] in
lemma Stamp_rotate_down (h:Screenlet P P' D)(hp:Stamp (N:=N) P' (C.localSection d) E y Y): Stamp (N:=N) P T (E ∘ D) y (cropStem D Y):=by
   refine ⟨hp.homes.high D h,?_,?_⟩
   · simp only [cropStem,Function.comp_apply,h.start]; exact hp.real'
   simp only [cropStem,Function.comp_apply,h.start]; exact hp.price
section
variable {Y: I⊕(C.labels.level d).Index→ Stem W G (C.S.side k p)}
   (i:I) (H:∀ i:ℕ,Solo (C.labels.level d) C.path p i) (L:Solvent (A:=A) X)
local notation "b'"=> (X.tone k).index ((H (C.ref d)).a)
local notation "V'"=> (H k).bar X (-(H (C.ref d)).a)
-- hull line for linear recomposition. preserves
include X H L
lemma score_mark (h : Fortune C A.W (waybill C.path.levels) N p k d y x η q X A.D H)
   (hv:y.Format 0 C.params (R k))(ht:y.remBound 0 (R k) (kappa C.path k) x)
   (hz:Stamp (N:=N) P' (C.localSection d) E y (Y (.inl i)))(hM:∀ j:V!, Stamp (N:=N) P' (C.localSection d) E ((X.tone k).plays (sonnet C X k j)) (Y (.inr j)))(hp:∀ j:V!, (Y (Sum.inr j)).home=(Y (.inl i)).home) {Z:Stem W G (C.S.side k p)}(hk:Stamp (N:=N) P' (C.localSection d) E V' Z)(hY:Z.home=(Y (.inl i)).home):
    let V := update (fun i:I=>Y (.inl i)) i Z;
    lights V= Deb.portion (atopBy W (foldTo i)) (spices P' (dyes (- b'))) (lights Y) ∧ Stem.ink V (R k)=Deb.portion (atopBy W (foldTo i)) (spices P' (dyes (- b'))) (Stem.ink Y (R k)):=by
   intro T'; have hg:= L.pull.earned k h.oldest h.limit; let X' := X.tone k; have hθ(i):=(hg.earns i).2; let t i:=(X'.plays i).exponentialEntry 0 (C.localSection d) (B); have hL:IsLinearMap ℂ t:=expoLinear X'.plays X'.charge hg.book hθ; let r i:=profile (C.path.rep N p k).activities (X'.plays i).forced; have hK : IsLinearMap ℂ r:= inkL X'.plays X'.charge hg.book hθ
   have he:(-(H (C.ref d)).a)=∑ j:V!, -(b' j) • sonnet C X k j:=by
       apply X'.index.injective; rw [map_neg,map_sum]; simp_rw [map_smul]; unfold sonnet; change -b'=∑ j, -(b' j) • (X.tone k).index ((X.tone k).index.symm _); simp_rw [LinearEquiv.apply_symm_apply,neg_smul,sum_neg_distrib, Size.sum_axes]
   obtain ⟨hT,hN⟩:=expo_on X L.pull y h (-(H (C.ref d)).a) hv ht
   constructor
   · funext ⟨v,j⟩; rw [branching]; by_cases hi:j=i; swap
     · rw [if_neg hi,add_zero]; exact congr_fun (congr_arg Stem.oil (update_of_ne hi Z (fun i=>Y (.inl i)))) v
     subst j; rw [if_pos rfl]; change (T' i).oil v=(Y (.inl i)).oil v+_; rw [show T' i=Z from update_self ..,(hk.rays T v).1,hY,(hz.rays T v).1,hT]; let o:= (Y (.inl i)).home v; let a:= P'.move v
     have hh(s d':Config G (C.S.side k p)→ℂ): radiant (alto C.path k d) a o (s+d')=radiant α a o s+radiant α a o d':=funext fun U=> by simp only [radiant,stepUp,Pi.add_apply,Pi.smul_apply,Motion.scalar_add,smul_eq_mul,mul_add]
     let c:= (X.tone k).index ((H (C.ref d)).a)
     let e:=sonnet C X k; let x' j:= t (e j)
     have hu : t (-(H (C.ref d)).a)=∑ j,(-(c j)) • (x' j):=Eq.trans (congr_arg t he) (by change (IsLinearMap.mk' t hL) _=_; rw [map_sum]; exact sum_congr rfl fun j _=> (IsLinearMap.mk' t hL).map_smul _ _)
     have hX(j):((Y (Sum.inr j)).oil v)=radiant α a o (x' j):= ((hM j).rays T v).1.trans (by rw [hp])
     change radiant α a o (_ + t _)=radiant _ a o _+∑ j, a.scalar (-(c j)) • ((Y (Sum.inr j)).oil v)
     rw [hu,hh,add_right_inj]; simp_rw [hX]; ext1 U; unfold radiant stepUp; simp only [Pi.smul_apply,Finset.sum_apply,pipes,Motion.scalar_mul,smul_eq_mul,Finset.mul_sum]; ring_nf -- sum normalize
   funext j; rcases j with ⟨v,j⟩; rw [branching]; by_cases hi:j=i; swap
   · rw [if_neg hi,add_zero]; exact congr_arg (profile _ ∘ (fun X: Stem W G _=> X.gas v)) (update_of_ne hi Z (fun i=>Y (.inl i)))
   subst j; rw [if_pos rfl]; change profile (C.path.rep N p k).activities ((T' i).gas v)=profile _ ((Y (.inl i)).gas v)+_; rw [show T' i=Z from update_self ..,(hk.rays T v).2,hY,(hz.rays T v).2]
   let o:= (Y (.inl i)).home v; let a:= P'.move v; let c:= b'; let ψ:=profile (C.path.rep N p k).activities; let N'(g:Res G (C.S.side k p)):= α • floatUp a o g
   let e:=sonnet C X k; let x' j:= r (e j)
   have hF : r (-(H (C.ref d)).a)=∑ j, (-(c j)) • (x' j):= Eq.trans (congr_arg r he) (by change (IsLinearMap.mk' r hK) _=_; rw [map_sum]; exact sum_congr rfl fun i _=> (IsLinearMap.mk' r hK).map_smul _ _)
   have hv(j): ψ ((Y (Sum.inr j)).gas v)=N' (x' j):= ((hM j).rays T v).2.trans (by rw [hp];rfl)
   have hh(s z: Res G (C.S.side k p)): N' (s+z)=N' s+N' z:=by unfold N' floatUp stepUp; funext j U; simp only [Pi.add_apply,Pi.smul_apply,Motion.scalar_add,smul_eq_mul,mul_add]
   change N' (profile (C.path.rep N p k).activities _)= N' _+∑ j,a.scalar (-(c j)) • ψ ((Y (.inr j)).gas v)
   rw [hN,show profile (C.path.rep N p k).activities ((X.tone k).plays _).forced= ∑ j, (-(c j)) • (x' j) from hF,hh,add_right_inj]; simp_rw [hv]; ext1 U; ext1 Y; unfold N' floatUp stepUp; simp only [Pi.smul_apply,Finset.sum_apply,pipes,smul_eq_mul,Motion.scalar_mul,Finset.mul_sum]; ring_nf
end
end YM.OPE.Allot
