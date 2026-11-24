import YM.RegulatorIR.Uniform.VacGap

/-! Triangular dependencies. Only an unintegrated same-order same-rank
input potentially survives without a strictly previous estimate. Pure
scalars not propagated. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Budget.Layer Diagram Budget.Packet Budget.Tuple Budget.Tariff Budget.Deck Post
open scoped BigOperators Topology Classical ENNReal
variable {W:Type}{I J : W→Type} {L: Meter W} {P:Post I J}

/-- Ordering where same-order higher rank goes first. Well-founded after
proved finite rank; not extended to arbitrary jets of unbounded rank. -/
def Earlier (e r p q:ℕ) := p<e ∨ p=e ∧ r<q
def Touch (e r p q:ℕ) := p<e ∨ p=e ∧ r≤q
lemma widen {e r p q:ℕ}(h:Earlier e r p q): Touch e r p q:= by unfold Touch Earlier at *; omega

-- incoming b-degree at same estimation? ancestors consumed only strictly earlier
variable (K:(w:W)→Layer (I w) (I w))
section Stack
variable {u b : ℕ}
variable (V:(w:W)→Orders (I w)) (Z:(w:W)→Orders (J w))
abbrev heatI (w:W) := logHeat (K w) (V w) false
abbrev shadeI (A:Post I J) (w:W):=logHeat (A.wrapK K w) (Z w) true

variable [∀ w,Fintype (J w)]
variable {e r:ℕ} (h: Beam L (P.cone (u+b+(u+b))) K)(hh:Poly L (P.weight b))
  (hk:∀ w,Layer.Sym (P.deck w) (P.deck w) (K w))
  (hx:∀ w,Vacuum (V w))(hy:∀ w,Vacuum (Z w))
  (hc:∀ p≤e,∀ r,Workday L (P.cone (u+b+(u+b))) fun w=> V w p r)
  (hz:∀ w p,p ≤ e→∀ r,(P.deck w).Ready (V w p r))
  (hb:∀ i j, Earlier e r i j→ 0<j → Claim L (P.pear u) 1 (P.vgap (fun w=>V w i j) (fun w=> Z w i j)))
include h hh hk hx hy hc hz hb
lemma part_vac (n i j:ℕ) (ht: Touch e r i j)(hp:0<j)(ha: n=0 → Earlier e r i j):
   Claim L (P.pear u) 1 (P.vgap (fun w=> heatI K V w n i j) fun w=> shadeI K Z P w n i j):=by
 induction n using Nat.strong_induction_on generalizing i j with
 | _ n ih=>
   cases n with
   | zero =>
      have HH :(j=0) = False:= propext (iff_false_intro (by omega))
      unfold heatI shadeI
      simp_rw [logHeat_first]; simp only [HH,false_and, ↓reduceIte]
      exact hb _ _ (ha rfl) hp
   | succ k=>
      have hBB (n l q:ℕ) (he:n≤e): Workday L (P.cone (u+b+(u+b))) fun w=>heatI K V w q n l:= Workday.hot hc h _ q n l he
      have hz' (w:W)(n l q:ℕ)(he:n≤e): (P.deck w).Ready (heatI K V w q n l):= heat_uses (hh:=hz w) _ _ _ (hk w) _ _ _ _ he
      have hh':i≤e:= by unfold Touch at ht;omega
      have hW := hBB i (j+2) k hh'
      let T:=fun w=>heatI K V w k i (j+2); let T' := fun w=>shadeI K Z P w k i (j+2)
      have hY (w:W):=(hz' w i (j+2) k hh')
      have he:Earlier e r i (j+2):= by unfold Earlier Touch at *; omega
      have hx' := ih k (by omega) i (j+2) (widen he) (by omega) (fun _=>he)
      have hQ := P.income (T:=T) (F:=T') (P.descent h (show u+b≤u+b+(u+b) from by omega)) hW hk hY hh hx' hp
      have hT:Claim L (P.pear u) 1 (P.vgap (fun w=> heating (K w) (heatI K V w k i) j) fun w=> heating (P.wrapK K w) (shadeI K Z P w k i) j):= gap_factor _ (gap_sym hQ (hW.loop_budget h) (fun w=>loop_ready (hY w) (hk w)))
      let t:=fun (l m:ℕ×ℕ) p (w:W)=>matchTwo (K w) (heatI K V w l.1 m.1) (heatI K V w l.2 m.2) j p
      have hm (l:ℕ×ℕ) (_:l∈Finset.antidiagonal k) (m:ℕ×ℕ) (hw:m∈Finset.antidiagonal i) p (_:p∈Finset.antidiagonal j): Workday L (P.cone (u+b+(u+b))) (t l m p):=by
          rcases p with ⟨p,q⟩; have hp:=Finset.mem_antidiagonal.mp hw
          exact Workday.with_match _ _ _ h (hBB _ _ _ (by omega)) (hBB _ _ _ (by omega))
      let K':=P.wrapK K
      let t':=fun (l m:ℕ×ℕ) p (w:W)=>matchTwo (K' w) (shadeI K Z P w l.1 m.1) (shadeI K Z P w l.2 m.2) j p
      have hf (l:ℕ×ℕ) (hl:l∈Finset.antidiagonal k)(m:ℕ×ℕ)(hw:m∈Finset.antidiagonal i) (p:ℕ×ℕ)(hs:p∈ Finset.antidiagonal j): Claim L (P.pear u) 1 (P.vgap (t l m p) (t' l m p)):= by
        by_cases hj₁:m.1=0; swap; by_cases hj₂:m.2=0; swap
        · have hhL:= Finset.mem_antidiagonal.mp hl; have hhP := Finset.mem_antidiagonal.mp hw; have hS:= Finset.mem_antidiagonal.mp hs; subst j
          have h₁:= hBB m.1 (p.1+1) l.1 (by omega); have h₂ := hBB m.2 (p.2+1) l.2 (by omega)
          have e₁:Earlier e r m.1 (p.1+1):= Or.inl (by omega); have e₂:Earlier e r m.2 (p.2+1):= Or.inl (by omega)
          have hΔ := (P.descent h (show u≤ u+b+(u+b) from by omega))
          have hE:= P.ahead hΔ hk (P.writes h₁ (by omega)) (fun w=>hz' w _ _ _ (by omega)) (P.writes h₂ (by omega)) (fun w=>hz' w _ _ _ (by omega)) (ih l.1 (by omega) _ _ (widen e₁) (by omega) (fun _=> e₁)) (ih l.2 (by omega) _ _ (widen e₂) (by omega) (fun _=>e₂)) hp
          unfold t t' matchTwo; simp only [↓reduceDIte]
          exact gap_factor _ (gap_sym hE (h₁.knot_budget h₂ h) fun w=>Packet.knot_ready _ (hz' w _ _ _ (by omega)) (hz' w _ _ _ (by omega)) (hk w))
        -- zero-vertex vanishing cases
        all_goals
          have hx'' (w:W)(i j):heatI K V w i 0 j=0:=Classical.byContradiction fun hi=> lt_irrefl 0 (heated_cap (K w) (V w) (hx w) false _ _ _ hi).1
          have hy' (w:W)(i j):shadeI K Z P w i 0 j=0:=Classical.byContradiction fun hi=> lt_irrefl 0 (heated_cap (P.wrapK K w) (Z w) (hy w) true _ _ _ hi).1
          have h1 (w:W) : t l m p w=0:=by by_contra! hi; rcases p with ⟨x,y⟩; obtain ⟨-,h',k'⟩:=match_comes hi; first | exact h' (by rw [hj₁,hx'']) | exact k' (by rw [hj₂,hx''])
          have h2 (w:W) : t' l m p w=0:=by by_contra! hi; rcases p with ⟨x,y⟩; obtain ⟨-,h',k'⟩:=match_comes hi; first | exact h' (by rw [hj₁,hy']) | exact k' (by rw [hj₂,hy'])
          rw [funext h1, funext h2]; unfold Post.vgap; simp_rw [Deck.desk_zero];simp only [sub_self]; exact Claim.zeroQ
      have htH : Workday L (P.cone (u+b+(u+b))) (fun w=>drift (K w) (heatI K V w) (heatI K V w) k i j):=Workday.sum _ _ (fun v hv=> Workday.sum _ _ (fun w hw=>Workday.sum _ _ fun y hy=>hm v hv w hw y hy))
      have htZ:Claim L (P.pear u) 1 (P.vgap (fun w=>drift (K w) (heatI K V w) (heatI K V w) k i j) fun w=>drift (K' w) (shadeI K Z P w) (shadeI K Z P w) k i j):=
        gap_sum _ (fun v hv=> gap_sum _ (fun w hw=> gap_sum _ (hf v hv w hw) (hm v hv w hw)) (fun w hw=> Workday.sum _ _ (hm v hv w hw))) (fun v hv=> Workday.sum _ _ fun w hw=> Workday.sum _ _ (hm v hv w hw))
      unfold heatI shadeI; simp only [logHeat_next, Nat.ne_of_gt hp, false_and, ↓reduceIte]; exact gap_factor _ (gap_plus hT (gap_factor _ htZ) (Workday.with_heat hW h) (htH.csmul _))
end Stack
end YM.RegulatorIR.Uniform
