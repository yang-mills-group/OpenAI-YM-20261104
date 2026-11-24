import YM.RegulatorIR.Uniform.Connection

/-! The main marked heat comparison induction. Unlike the capture estimates
this is still for a conditional Gaussian insertion, and contains no assumption
that distinct markers can be conditionally multiplied after this step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Diagram Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Budget.Deck Post
open scoped BigOperators Topology Classical ENNReal
variable {W:Type}{I J : W→Type} {L: Meter W} {P:Post I J}

section Stack
variable {u b e r:ℕ}
variable (K:(w:W)→Layer (I w) (I w))
  (V:(w:W)→ℕ→Orders (I w)) (Z:(w:W)→ℕ→Orders (J w))
  (T:(w:W)→Orders (I w))(F:(w:W)→ Orders (J w))
  {x:W→Room}{s v:W→ℝ≥0∞}
variable [∀ w,Fintype (J w)]
variable (h: Beam L (P.cone (u+b+b)) K)(hv:Carry L v (fun w=> s w*(P.toll x b w)⁻¹)) (hs:∀ w,s w≠⊤)
  (hk:∀ w,Layer.Sym (P.deck w) (P.deck w) (K w))
  (hx:∀ w k j, V w k 0 j=0)(hy:∀ w k j,Z w k 0 j=0)
  (hc:∀ p≤e,∀ r k,0<r → Workday L (P.cone (u+b+b)) fun w=> V w k p r)
  (hz:∀ w p,p ≤ e→∀ r k, 0<r → (P.deck w).Ready (V w k p r))
  (hd:∀ p≤e,∀ r k,0<r→Claim L (P.pear (u+b)) 1 (P.vgap (fun w=>V w k p r) (fun w=>Z w k p r)))
  (hT:∀ p≤e,∀ r,0<r → Claim L (P.rooted x (u+b+b)) s (fun w=>T w p r))
  (hb:∀ i j, Earlier e r i j→ 0<j → Claim L (P.anchored x u) v (P.agap (fun w=>T w i j) (fun w=>F w i j)))
-- change Claim.total_mark consumes V all incl scalar zero (logHeat true at e=0:scalar 0 yes); use hx all
include h hv hs hk hx hy hc hz hd hT hb
lemma part_mark (n i j:ℕ) (ht: Touch e r i j)(ha: n=0 → Earlier e r i j ∧ 0<j):
  Claim L (P.anchored x u) v (P.agap (fun w=> markHeat (K w) (V w) (T w) n i j) fun w=>markHeat (P.wrapK K w) (Z w) (F w) n i j):=by
 induction n using Nat.strong_induction_on generalizing i j with
 | _ n ih=>
   cases n with
   | zero=> simp_rw [markHeat_first];exact hb _ _ (ha rfl).1 (ha rfl).2
   | succ k=>
       let S (w:W) := markHeat (K w) (V w) (T w)
       let R:= P.wrapK K
       let S' (w:W) := markHeat (R w) (Z w) (F w)
       have hI:i≤e:=by unfold Touch at ht;omega
       have he : Earlier e r i (j+2):=by unfold Earlier Touch at *;omega
       have hα i j (hj:0 < j) (l:ℕ)(hp:i≤e) : Claim L (P.rooted x (u+b+b)) s fun w=> S w l i j:= Claim.total_mark T h hc hx hT l i j hp (fun _=>hj)
       have hW:= hα i (j+2) (by omega) k hI
       have hY:= ih k (by omega) _ _ (widen he) (fun _=>⟨he,by omega⟩)
       have hQ : Claim L (P.anchored x u) v (P.agap (fun w=>heating (K w) (S w k i) j) (fun w=>heating (R w) (S' w k i) j)):= gap_f _ (gap_same (simple_loop h hk hs hv hW hY) (Claim.loop_budget hW h) hs)
       let f:=fun (l m:ℕ×ℕ) p (w:W)=>matchTwo (K w) (S w l.1 m.1) (V w l.2 m.2) j p
       let f':=fun (l m:ℕ×ℕ) p (w:W)=>matchTwo (R w) (S' w l.1 m.1) (Z w l.2 m.2) j p
       have hm (l:ℕ×ℕ) (_:l∈Finset.antidiagonal k) (m:ℕ×ℕ) (hw:m∈Finset.antidiagonal i) p (_:p∈Finset.antidiagonal j): Claim L (P.rooted x (u+b+b)) s (f l m p):=by
          obtain ⟨p,q⟩:=p; have ht:= Finset.mem_antidiagonal.mp hw
          exact Claim.with_match _ _ _ h (hα _ (p+1) (by omega) _ (by omega)) (hc m.2 (by omega) _ _ (by omega))
       have hf (l:ℕ×ℕ) (hl:l∈Finset.antidiagonal k)(m:ℕ×ℕ)(hw:m∈Finset.antidiagonal i) (p:ℕ×ℕ)(hg:p∈ Finset.antidiagonal j): Claim L (P.anchored x u) v (P.agap (f l m p) (f' l m p)):= by
         rcases m with ⟨a,c⟩
         by_cases ht:c=0
         · subst c
           have h1 (w:W) : f l (a,0) p w=0 :=by by_contra! h'; obtain ⟨p,q⟩:=p; exact (match_comes h').2.2 (hx ..)
           have h2 (w:W) : f' l (a,0) p w=0 :=by by_contra! h'; obtain ⟨p,q⟩:=p; exact (match_comes h').2.2 (hy ..)
           rw [funext h1,funext h2]; unfold agap; simp_rw [Deck.scroll_zero,sub_zero]; exact Claim.zeroQ
         have hhP:= Finset.mem_antidiagonal.mp hw; change a+c=i at hhP
         have hh := Finset.mem_antidiagonal.mp hg; subst j
         have h₁:= hα a (p.1+1) (by omega) l.1 (by omega)
         have h₂:= hc c (by omega) (p.2+1) l.2 (by omega)
         have hL:= Finset.mem_antidiagonal.mp hl; have hb':Earlier e r a (p.1+1):= Or.inl (by omega)
         have H:= ih l.1 (by omega) _ _ (widen hb') (fun _=>⟨hb',by omega⟩)
         have he:= Post.narrow_node h hk hs hv h₁ H h₂ (fun w=> hz w _ (by omega) _ _ (by omega)) (hd c (by omega) (p.2+1) l.2 (by omega))
         unfold f f' matchTwo; simp only [↓reduceDIte]; apply gap_f; exact gap_same he (Claim.knot_budget h₁ h₂ h) hs
       have htH : Claim L (P.rooted x (u+b+b)) s (fun w=>drift (K w) (S w) (V w) k i j):=Claim.sum _ _ (fun l hv=> Claim.sum _ _ (fun m hw=> Claim.sum _ _ fun y hy=>hm l hv m hw y hy))
       have htZ:Claim L (P.anchored x u) v (P.agap (fun w=>drift (K w) (S w) (V w) k i j) fun w=>drift (R w) (S' w) (Z w) k i j):= gap_range _ (fun l hv=> gap_range _ (fun m hw=> gap_range _ (hf l hv m hw) (hm l hv m hw) hs) (fun m hw=> Claim.sum _ _ (hm l hv m hw)) hs) (fun l hv=> Claim.sum _ _ fun w hw=> Claim.sum _ _ (hm l hv w hw)) hs
       simp_rw [markHeat_next]; exact gap_f _ (gap_more hQ htZ (Claim.with_heat hW h) htH hs)
end Stack
end YM.RegulatorIR.Uniform
