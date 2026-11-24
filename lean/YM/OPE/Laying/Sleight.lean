import YM.OPE.Laying.Contrast
/-! # Contrast with capture: project exactly real regulator difference -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T :ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V}{A:Fibers I J} {s:Ward (Names V I)} {s':Ward (Names V J)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)} {z:Finset J}
variable (K : I)
namespace Mask
open Studio Pigment Playout Extra.Histories.Relay Next.Rank
local notation "Z'"=> C.labels.level d
set_option quotPrecheck false
-- next tuning declaration after erase.K identity.Not relative clip.Basis clock differs
variable {φS:I ⊕ (C.labels.level d).Index→ℕ}{W':ℕ→ I⊕(C.labels.level d).Index→ℝ}{P':∀ i:ℕ,I⊕(C.labels.level d).Index→Cup (C.path.rep N p i)}{F': I⊕(C.labels.level d).Index→ Config G (C.side N p)→ℂ}{u':∀ i:ℕ,I⊕(C.labels.level d).Index→ Site (C.side i p)}
-- accidental notation collision
variable {g:Extra.Histories.Music (C.labels.level d) C.path N p}
-- aquarium at i.Tone unit.S factory support at N.Board.
abbrev az (E: Extra.Histories.Music (C.labels.level d) C.path N p) (i:ℕ)(k: (C.labels.level d).Index) : (C.labels.level d).Coeff:= (E.tone i).index.symm (Size.axis (C.labels.level d) k)
local notation "v'"=> (g.tone i).index
local notation "az'"=> az g i
lemma storing_hue {K: (C.labels.level d).Coeff} : ∑ j:(Z').Index,v' K j • az' j=K:=by
    apply (g.tone i).index.injective; rw [map_sum]; simp_rw [map_smul ]; unfold az;simp only [LinearEquiv.apply_symm_apply]; exact GridApprox.coeff_sum C _ -- `v' K j` correct?
local notation "F'K"=> C.localSection d
local notation "E"=> standC C b N p
local notation "s!"=> (spectrum (E))
variable {s₀:Ward (Names (Site (C.side b p)) I)}
    (S:Ledger (standC C b N p) i (clash (recognize K) s₀) F' P' u' φS W' x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))
local notation "Wk"=> W' i (Sum.inl K)
abbrev applySign (d:ℕ)(F:I→ Config G (C.side N p)→ℂ)(x:C.label d) (K:I) (j:I):= if j=K then F j-C.O N p x 0 else F j
include S K h L
set_option maxHeartbeats 800000 in
lemma audition (hm:Stock.Tabs.opens C.path.levels 1 b q)(he:C.ref 0≤b)(hp:q ≤ φ K)(hk:φ K ≤ i)(hG:G.Simple)(ht:C.ref d ≤ q)
   (hV: Pitch s₀)(hS:Trial s₀)(hc:∀ k≠K,φ k=φS (.inl k)) (hu:∀ m,q ≤ m→m ≤ i → u' m (.inl K)=0)(hy':∀ i',u' i (.inr i')=0)
   (hz:∀ k≠K, ∀ j, W₀ j k=W' j (.inl k)) (hη:Lenient η₀ φ W₀)(hy:0<y)(h_y:y≤x)(hw:∀ j, φ K ≤ j→j ≤ i→ W₀ j K=road C i d Wk j)
   (ha:Minted C N p i d x' (u' i (.inl K)) (P' i (.inl K))) : -- edit assumptions
   ∀ (hr:Studio.Series C W (waybill C.path.levels) D N p d g), (∀ k: (C.labels.level d).Index, F' (.inr k)= C.O N p ((C.factory d N p).terminal (az' k)) 0 ∧ Studio.Mantle C.path N p i F'K (1,false) 0 ((g.tone i).plays (az' k)) (P' i (.inr k)))→
    y*W' i (.inl K)*‖alto C.path i d‖*stampOut C i d x' ≤ ζ d i→ (∀ l,y*W' i (.inl K)*(2*stampOut C i d x') ≤ x* W' i (.inr l)) →
    ∃ (c:C.label d), Next.UVStress.quota C d i N p c ≤ 2*stampOut C i d x' ∧
       (center C.S p ((hm.1.trans (hp.trans hk)).trans S.limit) 0).rootTest (C.beta N p) (applySign d (F' ∘ Sum.inl) c K K) ≤ stakes C b q/(road C i d (y*W' i (.inl K)) q) ∧
       ∃ F₀,Ledger (standC C b N p) i s₀ (applySign d (F' ∘ Sum.inl) c K) F₀ (fun i=> u' i ∘ Sum.inl) φ W₀ y D ∧ ∀ k≠K,∀ m,F₀ m k=P' m (.inl k):=by
    intro hr hf hP hy''; have hx:= hp.trans hk; have hN:= S.limit; have ht':= ht.trans hx; have hw':0 < y*W' i (.inl K):=mul_pos hy (S.clock.ready ..)
    let pK:= (P' i (.inl K)); let r:=road C i d (y*Wk)
    have hβ:=hu i hx le_rfl; rw [hβ] at ha
    obtain ⟨v,hv,Y',hE,⟨t,H,hQ,h_c⟩,hC⟩:= Minted.sign (u:=fun _=>0) (hx:=hN) L h ha ht hx hG hw' hP hr (fun i _ _=> ((C.path.levels.clock.op i p).ratio.root.map_zero).symm)
    let u:=(C.factory d N p).terminal v; let f:= v' v; let g':= applySign d (F' ∘ Sum.inl) (-u) K; let Q₀:= linear (recognize K) (inkC I f) (P' i); let Q₁ (k:(C.labels.level d).Index):= P' i (.inr k); let V':= linear (recognize K) (inkC I f) F'
    have hQ': Y' i=Q₀ K:=by rw [show Q₀ K=_ from saturation K (P' i) f (by simp)]; apply hC; exact storing_hue (g:=g) (i:=i) (K:=v) ▸ hr.homogeneity (m:=q) ht' hN _ f (az' ) Q₁ (fun i _=> (hf i).2) -- `apply` maybe wrong orientation
    have hV': V'=g':=by
        funext j; unfold g' applySign; split; rename_i ht; subst j; swap; · exact intensity K F' f _ ‹_› (by simp)
        rw [show V' K= _ from saturation K F' f (by simp)]; let pL:C.label d→ₗ[ℂ] Config G (C.side N p)→ℂ:= IsLinearMap.mk' (fun v=> C.O N p v 0) (C.linearO ..); change _=F' (Sum.inl K)-pL (-u); rw [map_neg,sub_neg_eq_add]; congr 1; simp_rw [(show ∀ k:(Z').Index,F' (Sum.inr k)=_ from fun k=>(hf k).1)]; let B:= pL.comp (C.factory d N p|>.terminal).toLinearMap; have he:= storing_hue (g:=g) (K:=v) (i:=i); change ∑ i,f i • B (az' i)=B v; rw [show B v=B (∑ i,f i • (az' i)) from (congr_arg B he).symm,map_sum]; simp_rw [map_smul]
    have hK : ∀ j, W₀ i j= W' i (.inl j):= fun j=>by by_cases h':j=K; subst j; rw [hw i hk le_rfl, born_road]; exact hz j h' i
    have hm'(k): ‖f k‖ ≤ 2* stampOut C i d x':=(by unfold f; have he:‖v' v k‖ ≤ (Z').coeffSize (v' v):= single_le_sum (fun i _=> norm_nonneg _) (mem_univ k); exact he.trans hv)
    have hw''(j:ℕ)(he:φ K ≤ j)(ht:j ≤ i) : lifted W₀ y j K=r j:=by unfold r lifted; rw [hw j he ht]; unfold road; ring
    have hProg : Program C.path N p (φ K) i (fun i=> u' i (.inl K)) Y' (fun m=>lifted W₀ y m K) D S.limit:=by
       refine ⟨fun i h h'=>?_⟩; rw [hu i (hp.trans h) h'.le, hu _ (hp.trans (h.trans i.le_succ)) h', hw'' _ (h.trans i.le_succ) h']; exact hE.follows i (hp.trans h) h'
    obtain ⟨Q',hq,hψ,h_p⟩:= blendLedger h K f S hS (hm.1.trans hp) hk hc hη hK hz hy h_y (fun l=> (mul_le_mul_of_nonneg_left (hm' l) hw'.le).trans (hy'' l)) (fun s=> by rw [hβ,hy' s]) hQ' (W₁:=W₀) hProg
    rw [show linear (recognize K) _ F'=g' from hV'] at hq
    refine ⟨-u,?_,?_,Q',hq,hψ⟩
    · rw [hr.quota i ht' hN (-u),map_neg,show ((C.factory d N p).terminal).symm u=v from LinearEquiv.symm_apply_apply ..,map_neg]; exact le_trans (le_of_eq (by simp [Labels.Frame.coeffSize])) hv
    apply holding L h hm hN hx he ht _ (hq.terms K) hQ (h_c q le_rfl hx) ?_ (fun _ _ _=> road_art hw' _) (fun i hi hm=> road_wealth L hG hw' (ht.trans hi)) hE
    have ht:=holdOneField (Θ:=standC C b N p) (u:=fun i=>u' i ∘ Sum.inl) (W₀:=lifted W₀ y) (P:=Q') h K hV hN hq.market hq.terms; rw [born_road]; change (E).Market _ _ _ _ _ _; have hξ: (u' i ∘ Sum.inl) K=0:= hβ; rw [show (fun _:Unit=>Y' i)=(fun _:Unit=>Q' i K) from (funext fun _=>(h_p i).symm),← hξ,← hK K]; exact ht
end Mask
end YM.OPE.Log.Book
