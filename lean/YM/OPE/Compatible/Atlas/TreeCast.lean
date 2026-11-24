import YM.OPE.Compatible.Atlas.Bear
/-!
# Standard atoms through varying spectators; arbitrary subset of incomparable slots. Explicit reflected variants available from Atom.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V J I:Type}[PartialOrder X][OrderBot X][Fintype X][Fintype J][Fintype I]
   (D:Origin X){Q:Finset X}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
variable {ψ:Filter V}{T: V→ℝ} {s: V→X→ℝ}(r:V→Viewers U)(y:V→ J→E4)(p:I→ C.book.Token)(q:J→ C.book.Token)
-- antichain criterion
structure Row (x:I→X): Prop where
    active i : x i∈ allUp D Q
    spaced i j : i≠j→¬ x i≤ x j
variable {z:I→X}(H: Burst D Q ψ T s) {η M c:ℝ}
include H
-- pack radius positive shorthand
lemma enough (hc:0<c)(h:0<η) : ∀ᶠ i in ψ, (∀ x∈Q,Real.exp (-(2:ℝ)*T i) ≤ η*s i x) ∧ η*s i ⊥ ≤ c ∧ ∀ x:X→E4,Ridge (s i) η M D Q x → ∀ i∈allUp D Q, ‖x i‖ ≤ c:=by
   have hb:= H.fresh η h; have he:=hb.fade _ hb.crowned.base; let R i:=s i ⊥; have hr:Tendsto R ψ (𝓝 0):=he.mono_right nhdsWithin_le_nhds
   have hf:Tendsto (fun i=> Real.exp (- T i)) ψ (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hb.ray)
   filter_upwards [H.fronts,hf.eventually (ge_mem_nhds h),(show Tendsto (fun i=> η*R i) ψ (𝓝 0) by simpa using hr.const_mul η).eventually (ge_mem_nhds hc),(show Tendsto (fun i=>M*R i) ψ (𝓝 0) by simpa using hr.const_mul M).eventually (ge_mem_nhds hc)] with i hi hz hl ht
   refine ⟨fun x hx=>?_,hl,fun x hx j hj=>?_⟩
   · rw [show -(2:ℝ)*T i= -T i + -T i from by ring,Real.exp_add]; exact mul_le_mul hz (hi _ hx) (Real.exp_nonneg _) h.le
   have he:= hx.near ⊥ j hb.crowned.base hj bot_le; rw [hx.belly,zero_sub,norm_neg] at he; exact he.trans ht
lemma cast_item (hR:Row D (Q:=Q) z) (hc:0<c)(hy:∀ᶠ i in ψ, ClearOf 0 (y i) c) (hη:0<η) (a:X)(ha:a∈allUp D Q): Scannable U D Q ψ T s η M 2 (fun i x=> observe (spectator U (r i)) (beside (x∘ z) (fun j=> x a+y i j)) (beside p q)):=by
    let W:= I⊕ J; let f:W → X:=beside z (fun _=>a); let l i:=beside (fun _ : I=> (0:E4)) (y i); let e:= runNames W; let A:Atom U X V:=⟨Fintype.card W,f ∘ e,fun i=>l i∘ e,(beside p q) ∘ e,r⟩
    have he:=enough D H (M:=M) (show 0<c/4 by positivity) hη; refine ⟨.one A,?_⟩; filter_upwards [he,hy,(time_bright D (H.fresh _ hη)).lit] with i ⟨he,hf,hw⟩ hi hV x hX
    let u k:= x (f k)+l i k; let v:= beside (x ∘ z) (fun j=> x a+y i j); have hq : u=v:=funext fun j=> by cases j<;>simp [u,v,f,l]
    -- use bound via shared ancestor, all. sufficient
    have hr(j k:W)(hj:j≠k): ∃ b∈Q,b ≤ f j ∧ b ≤ f k ∧ η*s i b ≤ ‖u j-u k‖:=by
       have h (j:I)(k:J): η*s i ⊥ ≤ ‖x (z j)-(x a+y i k)‖:=by
          have hy:= hi.openSpace k; rw [zero_sub,norm_neg] at hy; have ht:=hw x hX _ ha; have hv:=hw x hX _ (hR.active j); have h1:‖y i k‖-‖x a‖ ≤ ‖x a+y i k‖ :=by simpa [add_comm] using norm_sub_norm_le (y i k) (-x a)
          have h2:= norm_sub_norm_le (x a+y i k) (x (z j)); rw [norm_sub_rev (x (z j))]; linarith only [hy,h1,h2,ht,hv,hf,hc]
       match j,k with
       | .inl j,.inl k=>
          have hi:j≠k:=fun e=>hj (congr_arg _ e); have hp:=hR.spaced j k hi; have he:= diverge D (Burst.crown D H) (hR.active j) hp; refine ⟨_,he,coupled_left D (z j) (z k),coupled_right D (z j) (z k),?_⟩; rw [hq]; exact hX.span _ _ (hR.active j) (hR.active k) hp (hR.spaced k j hi.symm)
       | .inr j,.inl k=> refine ⟨⊥,Burst.crown D H|>.base,bot_le,bot_le,?_⟩; rw [hq,norm_sub_rev]; exact h k j
       | .inl j,.inr k=> refine ⟨⊥,Burst.crown D H|>.base,bot_le,bot_le,?_⟩; rw [hq]; exact h j k
       | .inr j,.inr k=>
           refine ⟨⊥,Burst.crown D H|>.base,bot_le,bot_le,?_⟩; change _ ≤ ‖(x a+y i j)-(x a+y i k)‖; rw [add_sub_add_left_eq_sub]; exact le_trans hf ((by linarith only [hc] : c/4 ≤ c).trans (hi.spread _ _ (fun e=>hj (congr_arg _ e))))
    have ht : Atom.Quota A D Q (s i) i x η (Real.exp (-2*T i)):=by
       have hh(j k:Fin A.n)(h:j≠k):∃ b∈Q, b≤A.hang j ∧ b ≤ A.hang k ∧ η*s i b ≤ ‖A.weight i x j k‖:=hr (e j) (e k) (e.injective.ne h)
       refine ⟨fun j k h=>(hh j k h).elim fun b ⟨hb,hk,hj,hf⟩=> (he b hb).trans hf, fun j k h w hw=>?_⟩; obtain ⟨b,hb,hj,hk,he⟩:=hh j k h; exact le_trans (mul_le_mul_of_nonneg_left (dim_forks D (Burst.crown D H) hV hj hk hw) hη.le) he
    have hφ:Injective u:=fun j k hh=> Classical.byContradiction fun he'=> (let h:=hr j k he'; not_le_of_gt (Real.exp_pos (-2*T i)) ((he _ h.choose_spec.1).trans ((h.choose_spec.2.2.2).trans_eq (by rw [hh,sub_self,norm_zero]))))
    refine ⟨?_,fun g h=>by rw [show g = _ from Finset.mem_singleton.mp h]; exact ht⟩; change observe _ (A.pose i x) _ = observe _ v _; rw [← hq]; exact perm_observe (spectator U (r i)) (spectate U _).laws.toSymmetric e (beside p q) hφ
end YM.OPE.Arboreal.Trace
