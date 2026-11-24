import YM.OPE.Laying.Dock
/-! # Landing all awake slots (true formed story) -/
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
variable (S:Ledger Θ (j+1) (pullback A s') F P u φ W₀ x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))

local notation "Γ"=> (fun i=> (Y).clock.hatBeta (i+1))
-- x in k+1 widths
-- specify Whitney.Envelope, once
noncomputable def resQuote (C:Family G) (i d:ℕ) (x:ℝ):= C.S.a (i+1)^d*((C.path.levels.clock.hatBeta (i+1))*(1/(2*x)))
structure Minted (C:Family G)(N p i:ℕ)(d:ℕ)(x:ℝ) (o:Site (C.side i p)) (Q:Cup (C.path.rep N p i)) : Prop where
    bound : ∃ A:Coefficient (C.labels.level d) (C.side i p), A.Format 0 C.params (C.path.rep N p i) ∧ A.remBound 0 (C.path.rep N p i) (kappa C.path i) (resQuote C i d x) ∧ (C.labels.level d).coeffSize A.x ≤ resQuote C i d x ∧ Studio.Mantle C.path N p i (C.localSection d) (1,false) o A Q
variable (U: Release Θ A z s' i j L φ u) (d':J→ℕ)
local notation "p'"=> (lineRelease A ∘ W₀)
include h S U
lemma Release.land (hb:T>0)(hT:Fintype.card I ≤ T) (hG:G.Simple)(ht:∀ a∉z,C.ref (d' a) ≤ i) (hx':0<x')(hf:x'≤ (cell C.path (i+1) j (T+2) (peer L T j) x)^T)(hc:x'≤x) -- at RunBudget. always ν or smaller.
    (hy:0<y)(hz:4*y*Γ i ≤ x')(hk:0<α)(hr:α≤ δ₀ i*η₀ i*y) : ∃ X, Θ.Market s' (u i∘A.twig) X (Θ.intention (grouped_X F A) i ((i.le_succ.trans U.prep.le).trans (Nat.le_of_lt S.limit))) (lifted (fun i=>lineRelease A (W₀ i)) α i) (ν i) ∧ (∀ k∈z,X k=P i (A.twig k)) ∧ ∀ k∉z,Minted C N p i (d' k) (x'*lineRelease A (W₀ (i+1)) k) (u i (A.twig k)) (X k):=by
     have h₁:=U.funded; have h₂:=U.beginning; have h₃:=U.prep; have hl:= L.guide h h₁.le; have hN:j<N:= S.limit; have ht₀:= hl.params i h₂; have he':=h₃.trans hN; have hi:= Nat.lt_of_succ_lt he'; let Δ:= C.path.levels.clock.op i p; obtain ⟨F',hF,hK,hA⟩:= Release.race L h S U T hG hT hb hx' hf -- remove k
     have hr'(k:J)(he:k∈z) m: lineRelease A (W₀ m) k= W₀ m (A.twig k):=by unfold lineRelease; rw [(U.lights k he).content,prod_singleton]
     have hh(k:J)(he:k∉z): lineRelease A (W₀ i) k=lineRelease A (W₀ (i+1)) k:=by
        apply prod_congr rfl; intro j' hj; let H:=S.clock; have he': φ j'=j:= U.prompt j' (fun hp=>he (((A.focuses ..).1 hj) ▸ hp)); exact (H.early _ _ (by omega)).trans (H.early _ _ (by omega)).symm
     let U₀:= lifted (p') α i; let V':J→ℝ:= lifted (p') y (i+1); have hQ:1 < Γ i:=(Y).fits.delayed _; have h_y:y≤ x':= (by linarith only [hy,hz,mul_lt_mul_of_pos_left hQ hy]); have h_α:α ≤ δ₀ i*y:= hr.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (ht₀.2.2.1.le) ht₀.2.1) hy.le)
     have hP(m k):0< lineRelease A (W₀ m) k:=prod_pos fun i _=>S.clock.ready ..; have hV(k):0<V' k:=mul_pos hy (hP ..); have hβ:0<Γ i:= zero_lt_one.trans hQ; have hx0(k):= (mul_pos hx' (hP (i+1) k))
     have hw(k:J):∃ v p₁,Cup.Edge Δ (D N p i hi) (F' k) v ((u (i+1) ∘ A.twig) k) ((u i ∘ A.twig) k) p₁ (V' k)∧ (k∈z→v=P i (A.twig k))∧ (k∉z→ Minted C N p i (d' k) (x'* p' (i+1) k) (u i (A.twig k)) v):=by
        by_cases hK':k∈z
        · obtain ⟨p,hp⟩:= (S.progress (A.twig k)).follows i (U.sleeper _ (A.sectioned k |>.symm ▸ hK')) (by omega);
          have hμ: V' k=y* W₀ (i+1) (A.twig k):=congr_arg (y*·) (hr' _ hK' _); refine ⟨P i (A.twig k),p, ?_,fun _=>rfl, fun hv=>(hv hK').elim⟩; rw [hK _ hK']; exact hp.thin (hV k|>.le) (hμ.trans_le (mul_le_mul_of_nonneg_right (h_y.trans hc) (S.clock.ready ..|>.le)))
        let q:= u i (A.twig k); let X:= x'* p' (i+1) k;
        have hv : (u (i+1) ∘ A.twig) k=Δ.ratio.embed q:=U.hope k hK'
        have hs:4*(V' k)*(1/(2*X))≤1 := by
          have hh:0<X:= hx0 k; have ht':2*y ≤ x':=by linarith only [mul_lt_mul_of_pos_left hQ hy,hz,hy]
          change 4*V' k*(1/(2*X)) ≤ _; rw [← mul_div_assoc]; refine (div_le_one (by positivity)).2 ?_; change 4*(y*(lineRelease A (W₀ (i+1)) k))*1 ≤ 2*X; unfold X; change _ ≤ 2*(x'* lineRelease A (W₀ (i+1)) k); nlinarith only [mul_le_mul_of_nonneg_right ht' (hP (i+1) k|>.le)]
        have hz0: V' k*(Γ i * (1/(2*X))) ≤ 1:=by
          have hh:0<X:= hx0 k; change _ ≤ _; rw [← mul_assoc,← mul_div_assoc]; apply (div_le_one (show 0 < 2*X by positivity)).2; let w:=lineRelease A (W₀ (i+1)) k; have hw:0<w:=hP ..
          change y*w*Γ i*1≤2*(x'*w); nlinarith only [mul_le_mul_of_nonneg_right hz hw.le,mul_pos hx' hw] -- first inequality hz* uses factor4
        obtain ⟨B,v,ht,hξ,hμ,hΩ,hΓ⟩:= L.writtenOrigin h (ht k hK') hi q (hv ▸ (show Blade (Ξ (i+1)) ((u (i+1)∘A.twig) k) (F' k).home (F' k).leaves 0 (1/(2*X)) from hA k hK')) (y:=V' k) hs hz0 (hV k)
        exact ⟨v,0,hv.symm ▸ hΓ, fun u=>(hK' u).elim,fun _=>⟨B,ht,hξ,hμ,hΩ⟩⟩
     choose Y' φ' hΓ hW hX using hw
     have hp:=U.clearances i le_rfl (by omega); let y':=(u (i+1)∘A.twig); have hS:V' ≤ (fun k=> x'*lineRelease A (W₀ (i+1)) k):= fun k=>mul_le_mul_of_nonneg_right h_y ((hP ..).le)
     have hφ:= hF.shy Θ hV hS le_rfl; have hv:=occupied_trans hp.1 A; have ht':= Θ.paidFor (grouped_X F A) hl.well (cont F A S.terms) hi; have hz:= hφ.strides Θ h.wilson hl.host h₂ h₂ hi (by linarith only) ht' (fun k => S.slots i h₂ (by omega) _) (occupied_trans hp.2 A) hv hΓ
     have hu(k):0<U₀ k:=mul_pos hk (hP i k); have hh(k:J): U₀ k ≤ δ₀ i* V' k:=by
        unfold U₀ V' lifted; dsimp only [Function.comp_apply]; by_cases he:k∈z; swap; · rw [hh k he,← mul_assoc (renal C.path.levels i) y _]; exact mul_le_mul_of_nonneg_right h_α ((hP ..).le)
        simp_rw [hr' _ he]; refine (mul_le_mul_of_nonneg_right hr (S.clock.ready ..|>.le)).trans ?_; have h':= (S.clock.paid (A.twig k) i); exact by linarith only [mul_le_mul_of_nonneg_left h' (mul_pos ht₀.2.2.1 hy|>.le)]
     refine ⟨Y', ?_,hW,hX⟩; rw [Θ.intention_step _ hi]; exact (hz.peek Θ h.wilson hl.host h₂ h₂ hi hv U.game hu (fun k hx he t ht=>(prod_le_prod (fun j _=> hu j.snd|>.le) (fun j _=> hh j.snd)).trans (le_mul_of_one_le_right (prod_nonneg (fun j _=>(hu ..|>.le).trans (hh j.snd))) (Real.one_le_exp (by positivity))) ) ).shy Θ hu le_rfl (by linarith only)
end YM.OPE.Log.Book
