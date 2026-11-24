import YM.MergeProof.Chalet
/-!
# Re-rendering on this same Actual. Flag-Updates when even *one* address widens.

Adapter from `Merger/Tongue`, `Guards`. Private combinatorial bubble for the
scratch booking (existing alphabet has ALL the slots required by our packings;
no global Reserve). Rents back FULL flagged tests before anything is read.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Dilation
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local YM.MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{ι:Type*}{d:ℕ}{F:Labels.Frame G d}{o:Site n}{B:SectionData F}
    {R:Rep G n}
private abbrev glass (A:Activities G n) := { A with forced:=fun i=> {A.forced i with extraTest:=fun _ => True} }
private abbrev glassPlate (R:Rep G n) := { R with activities := glass R.activities }
private def crossed (A : Activities G n) {ι : Type*} (X : ι → Support n) : Letters (glass A) X ≃ Letters A X :=
  Equiv.sigmaCongrRight fun _i => (Equiv.refl (Finset ℕ)).subtypeEquiv
    (fun _x => ⟨fun h => ⟨h.1,h.2,h.3⟩,fun h => ⟨h.1,h.2,h.3⟩⟩)
private def cusps {X:ℕ→Support n} (S : Berths R.p R.activities X) : Push.Local.Slots (glassPlate R).activities X where
  label := (crossed R.activities X).toEmbedding.trans S.label
  support u := S.support ((crossed R.activities X) u)
  inventory u := S.inventory ((crossed R.activities X) u)
  allows _ _ := trivial

private lemma caput {X:ℕ→Support n} (Y:Berths R.p R.activities X) (p:ℕ→ Config G n→ℂ) (hs:Dominated ((cusps Y).pack R.p.threshold p)):
   profile R.activities ((cusps Y).pack R.p.threshold p)= hook R.activities R.p.threshold (clipSum X p):=by
   let A:= R.activities; let T:=cusps Y; let x:=R.p.threshold
   have hev(q U): T.pack x p (Y.label q) U=p q.1 U*grasp A x (X q.1) q.2.val (fusionBox A (X q.1) q.2.val) U:=by
     let J:=crossed A X; obtain ⟨i,rfl⟩:= J.surjective q
     rw [show Y.label (J i)= T.label i from rfl,T.pack_label]
     unfold Slots.payload; change _ = p i.1 U*grasp A x (X i.1) i.2.val (fusionBox A (X i.1) i.2.val) U; unfold grasp
     have hP: Local.Packs A (X i.fst) (i.2.val):=(J i).2.property
     have he : ((glassPlate R).activities.forced (T.label i)).eligible x U ↔ (fusionBox A (X i.fst) (i.2.val)).1∩flags x U=(fusionBox A (X i.fst) (i.2.val)).2:=by
          unfold ForcedAddress.eligible
          rw [show ((glassPlate R).activities.forced (T.label i)).support = _ from T.support i, show ((glassPlate R).activities.forced (T.label i)).inventory = _ from T.inventory i]; exact ⟨fun h=> h.1,fun h=>⟨h,trivial⟩⟩
     split_ifs with h h'
     · rfl
     · exact (h' ⟨hP,rfl,he.1 h⟩).elim
     · rename_i h'; exact (h (he.2 h'.2.2)).elim
     rw [mul_zero]
   apply toll (e:= Y.label) (fun i=>Prod.ext (Y.support _) (Y.inventory _)) hev (fun i hi=> ?_) hs
   apply Push.Local.Slots.pack_none
   rintro ⟨i,h⟩; exact hi ⟨crossed R.activities X i,h⟩
variable {σ C Λ δ η w e r v : ℝ}
private theorem lawful (hx : R.Lawful σ C Λ δ η) : (glassPlate R).Lawful σ C Λ δ η := by
  let K := (glass R.activities)
  have hu := hx.labels
  have hf := hu.forced
  have he : K.ForcedFamily R.p := ⟨hf.sym, fun _ _ _ => Iff.rfl, hf.meas, fun _ => MeasurableSet.univ, hf.reads, fun _ _ _ _ _ => rfl,
    fun i U h => ⟨(hf.permit i U h).1,trivial⟩⟩
  refine ⟨hx.paths,⟨hu.regular.smooth,hu.regular.at_flat,hu.regular.vanish⟩,he,fun s o => ?_,hu.boundE,hu.boundK⟩
  obtain ⟨m⟩ := hu.moves s o
  exact ⟨m.ep,m.kp,m.reg_site,m.reg_support,m.forced_support,m.forced_inventory,fun _ _ => Iff.rfl,m.valuesE,m.valuesK⟩

variable {M:Local.Raw F n}{X:ℕ→Support n}(S:Berths R.p R.activities X)
def rented (f:ℕ→ Config G n→ℂ): ℕ→ Config G n→ℂ:= (cusps S).pack R.p.threshold f
-- Pack under this width.Bubble R. Supports unchanged etc. Pay exact merging.
lemma cover (p:ℕ→ Config G n→ℂ) (h:∀ i, Local.Attaches R.p.threshold (X i) (p i)) (hf:∀ i,o ∈ X i) (a:ℕ→ℝ) (hh:∀ i,0 ≤ a i ∧ ∀ U, ‖p i U‖ ≤ a i) (hb:SumBudget (fun i=> reservedMass R.p (X i) (a i)) v)
    (hw:R.Lawful σ C Λ δ w) (hP:0≤ w) (ht:Local.hitWidth R.p *w≤1):
    ForceFormat R.p R.activities o (rented S p)∧ ForceCost R.p R.activities (rented S p) (hitWidth R.p*w*v) ∧ profile R.activities (rented S p)=hook R.activities R.p.threshold (clipSum X p) ∧ Attainment R.p o (clipSum X p) v ∧ ∀ U:Config G n,HasSum (fun b'=> gasMark R.p R.activities U b' (rented S p)) ((∑' i,p i U)*(R.activities.gas R.p U:ℂ)):=by
   let X':= X; let T:= cusps S; let f := rented S p
   have hx:= lawful hw
   have hA:= S
   have hr i: Attaches (glassPlate R).p.threshold (X i) (p i):= h i
   have hT:= T.forceFormat hx.labels.forced hf hr; change ForceFormat (glassPlate R).p (glassPlate R).activities o f at hT
   have hη:= width_one_le R.p; have hM:SumBudget (fun i=> mergePrice R.p w (X i) (a i)) (hitWidth R.p *w*v):= Local.sumBudget_mono (Local.sumBudget_mul_left hb (mul_nonneg (zero_le_one.trans hη) hP)) (fun i=> mergePrice_nonneg _ _ hP (hh _|>.1)) (fun i=> price_meeting hP ht (hh _|>.1) (X i)) le_rfl
   have hq : ForceCost R.p R.activities f (hitWidth R.p*w*v):=by
        let T':Berths R.p R.activities X:=S; change ForceCost (glassPlate R).p (glassPlate R).activities _ _
        exact T.forceCost hx.labels.boundK hM (fun i=>(hh i).1) (fun i=>(hh i).2) -- order
   have hd : Dominated f:=by
       obtain ⟨a,ha,h⟩:=hq
       exact ⟨_,ha.2.1,fun j U=>(h j|>.2 U).trans (R.p.loMass _ _ (h j|>.1))⟩
   have hs:Summable a:=hb.2.1.of_nonneg_of_le (fun i=>(hh i).1) (fun i=> le_mul_of_one_le_left (hh i|>.1) (Real.one_le_exp (mul_nonneg (by linarith only [R.p.exponent_pos] : 0≤ R.p.supportExponent+2) (by positivity))))
   refine ⟨⟨?_,hT.carried,hT.invariant,hT.supported,hT.borel⟩,hq,caput S p hd, ?_, fun U=>?_⟩
   · intro i U hi; have he:(glass R.activities|>.forced i).eligible R.p.threshold U:= hT.forcing i U hi
     obtain ⟨s,hs⟩ : ∃ s,S.label s=i := by
       by_contra hn
       exact hi (by unfold rented; rw [Push.Local.Slots.pack_none _ _ _ _ ?_]; rfl; rintro ⟨q,hq⟩; exact hn ⟨crossed _ _ q,hq⟩)
     subst i; exact ⟨he.1,S.pass s U he.1⟩
   · have hu(Z:Support n)(i:{i// X i=Z}): Attaches R.p.threshold Z (p i.val):=(congr_arg (fun j=> Attaches R.p.threshold j (p i.val)) i.property).mp (h i.val)
     refine ⟨fun i=> ⟨fun U V hA ht=>tsum_congr (fun j=>(hu i j).sites U V hA ht),fun g U=>tsum_congr (fun j=> (hu i j).symmetry g U),Measurable.tsum (fun j=>(hu i j).borel),fun U hU=> (tsum_congr (fun j=>(hu i j).healthy_zero U hU)).trans tsum_zero⟩,fun i hi=>?_,?_⟩ -- test
     · by_contra hg; haveI : IsEmpty {j// X j=i}:=⟨fun ⟨j,H⟩=>hg (H ▸ hf _)⟩
       apply hi; funext U; unfold clipSum cram; rw [tsum_empty];rfl
     let g i:= reservedMass R.p (X i) (a i)
     have hp:Summable g:= hb.2.1
     have hG:=heavy X hp; have hi (i:Support n) : reservedMass R.p i (cram X a i)=cram X g i:=by unfold reservedMass cram; rw [← tsum_mul_left]; exact tsum_congr (fun j=>congr_arg (fun Z=>reservedMass R.p Z (a j.val)) j.property.symm)
     refine ⟨cram X a, ⟨fun i=> mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun j=>(hh j.val).1)),(by simp_rw [hi]; exact hG.summable),(by simp_rw [hi,hG.tsum_eq]; exact hb.2.2)⟩,fun i=>⟨tsum_nonneg (fun j=>(hh j.val).1),fun U=> metric_cram _ hs (fun j=>(hh j).2 U) i⟩⟩
   exact T.recover (glassPlate R).p U p hr hx.labels (hs.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>(hh i).2 U))
-- Combining rebates into an Odyssey. Keep support oriented. Doesn't need ledger for presumed pole.
lemma attainAdd {f g:Response G n}(h:Attainment R.p o f v)(hh:Attainment R.p o g w): Attainment R.p o (f+g) (v+w)∧ hook R.activities R.p.threshold (f+g)=hook R.activities R.p.threshold f+hook R.activities R.p.threshold g:=by
    obtain ⟨s,hs,hS⟩:=h.toll; obtain ⟨q,hq,hQ⟩:=hh.toll
    refine ⟨⟨fun i=>?_,fun i hi=> ?_,fun i=>s i+q i, ?_,fun i=>⟨add_nonneg (hS i|>.1) (hQ i|>.1), fun U=>(norm_add_le _ _).trans (add_le_add (hS i|>.2 U) (hQ i|>.2 U))⟩⟩,?_⟩
    · have hp:=h.shaped i; have hs':=hh.shaped i
      exact ⟨fun U V hA ht=>congr_arg₂ (·+·) (hp.sites U V hA ht) (hs'.sites U V hA ht),fun g U=>congr_arg₂ (·+·) (hp.symmetry ..) (hs'.symmetry ..),hp.borel.add hs'.borel,fun U hU=>by rw [Pi.add_apply,Pi.add_apply,hp.healthy_zero U hU,hs'.healthy_zero U hU,add_zero]⟩
    · by_contra hp; exact hi (by rw [Pi.add_apply,not_not.mp (mt (h.marked i) hp), not_not.mp (mt (hh.marked i) hp),add_zero])
    · simpa only [reservedMass,mul_add] using! Local.sumBudget_add hs hq
    funext i U; simp [hook,add_mul,sum_add_distrib]
end YM.LocalLTE.Dilation
