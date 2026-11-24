import YM.RegulatorIR.Uniform.RelaxVac

/-! Transmission of a full source numerator. It is legal to take a whole
multi-mark presentation as the given insertion; do not transmit its slots
under independent kernels. Polynomial degree bounds here still coefficient
bills. Scalar inheritance doesn't enter a nonzero heat power. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform
open Function Budget Diagram Budget.Packet Budget.Tuple Budget.Layer Post
open scoped BigOperators Topology Classical ENNReal
variable {W:Type}{I J: W → Type}{L: Meter W}{r : ℕ}
namespace Claim
variable {K : (w:W)→Layer (I w) (I w)} {A : (w:W)→Tariff (I w)} {B:(w:W) → Premium (A w)} {u:W→ℝ≥0∞}
lemma with_heat {T:(w:W)→ Ranked (I w)} (h:Claim L B u (fun w=>T w (r+2)))(hh:Beam L A K): Claim L B u (fun w=>heating (K w) (T w) r):= Claim.csmul (Claim.robust (Claim.loop_budget h hh)) _
lemma with_match {T S:(w:W)→ Ranked (I w)} (r p q:ℕ) (hh: Beam L A K) (h: Claim L B u (fun w=>T w (p+1)))(hs:Workday L A (fun w=> S w (q+1))): Claim L B u (fun w=>matchTwo (K w) (T w) (S w) r (p,q)):=by
 by_cases he : p+q=r
 · subst r; simp only [matchTwo, ↓reduceDIte]; exact Claim.csmul (Claim.robust (Claim.knot_budget h hs hh)) _
 simp_rw [matchTwo,dif_neg he]; exact zeroQ
-- only strict predecessor inputs through e,r needed
lemma from_mark {e r:ℕ}{V:(w:W)→ℕ→Orders (I w)} (T:(w:W)→Orders (I w))(h:Beam L A K) (hp:∀ p≤e,∀ i j,0 < i → Workday L A (fun w=>V w j p i))
    (hV:∀ w k i, V w k 0 i=0) (hf:∀ i j, Earlier e r i j → 0<j → Claim L B u (fun w=> T w i j)) (k i j:ℕ)(hk:Touch e r i j)(hx:k=0 → Earlier e r i j ∧ 0<j):
   Claim L B u (fun w=>markHeat (K w) (V w) (T w) k i j):=by
 induction k using Nat.strong_induction_on generalizing i j with
 | _ k ih=>
    cases k with
    | zero=> simp_rw [markHeat_first]; exact hf i j (hx rfl).1 (hx rfl).2
    | succ k=>
       have ht:i≤e:=by unfold Touch at hk; omega
       have h': Earlier e r i (j+2):= by unfold Touch Earlier at *; omega
       simp_rw [markHeat_next]
       apply Claim.csmul; apply Claim.add (with_heat (ih k (by omega) i (j+2) (widen h') (fun _=>⟨h',by omega⟩)) h)
       unfold drift carry force; apply Claim.sum
       rintro ⟨p,q⟩ hy; have he:=Finset.mem_antidiagonal.mp hy; change p+q=k at he;apply Claim.sum
       rintro ⟨a,b⟩ hv; have hh:= Finset.mem_antidiagonal.mp hv;change a+b=i at hh;apply Claim.sum
       rintro ⟨s,t⟩ hw
       change Claim _ _ _ (fun w=> matchTwo (K w) (markHeat (K w) (V w) (T w) p a) (V w q b) j (s,t))
       by_cases hb:0<b
       · have hQ: Earlier e r a (s+1):=Or.inl (by omega)
         exact with_match _ _ _ h (ih p (by omega) a _ (widen hQ) (fun _=>⟨hQ,by omega⟩)) (hp b (by omega) (t+1) q (by omega))
       have hb':b=0:=by omega
       subst b
       convert Claim.zeroQ using 1; ext1 w; by_contra! hp'
       obtain ⟨-, -,h''⟩:=Diagram.match_comes hp'
       exact h'' (hV w _ _)
-- Mark bounds with no request on scalar part at input, Cover or orbit.
lemma total_mark {e:ℕ}{V:(w:W)→ℕ→Orders (I w)} (T:(w:W)→Orders (I w))(h:Beam L A K) (hp:∀ p≤e,∀ i j,0 < i → Workday L A (fun w=>V w j p i))
    (hV:∀ w k i,V w k 0 i=0)(hf:∀ i ≤ e, ∀ j,0<j → Claim L B u (fun w=> T w i j)) (k i j:ℕ)(hk:i ≤ e)(hx:k=0 → 0<j):
   Claim L B u (fun w=>markHeat (K w) (V w) (T w) k i j):=by
 apply from_mark T h hp hV (r:=0) (k:=k) (fun i j he=> hf i (by unfold Earlier at he;omega) j)
 · unfold Touch; omega
 intro h; specialize hx h; unfold Earlier; omega
end Claim

namespace Post
variable (A:Post I J)
def agap (T:(w:W)→Packet (I w) r)(F:(w:W)→Packet (J w) r) w:= F w-(A.deck w).scroll (T w)
variable {A} {s v : W→ℝ≥0∞}{x: W→Room}{u k b:ℕ}
lemma gap_f {T:(w:W)→Packet (I w) r}{F:(w:W)→Packet (J w) r}(c:ℝ)(h:Claim L (A.anchored x u) v (agap A T F)): Claim L (A.anchored x u) v (agap A (fun w=>c • T w) fun w=> c • F w):=by
 unfold agap; simp_rw [Deck.scrolling,← smul_sub]; exact h.csmul _
lemma gap_more {T S:(w:W)→Packet (I w) r}{F G:(w:W)→Packet (J w) r}
 (h:Claim L (A.anchored x u) v (agap A T F))(hh:Claim L (A.anchored x u) v (agap A S G))(hp:Claim L (A.rooted x k) s T)(ht:Claim L (A.rooted x k) s S)(he:∀ w,s w≠⊤): Claim L (A.anchored x u) v (agap A (fun w=>T w+S w) fun w=>F w+G w):=by
 convert h.add hh using 1; ext1 w; unfold agap
 rw [Deck.scroll_sup (A.deck w) (ne_top_of_le_ne_top (hp.cost w (he w)) (quota_mono _ fun _=>(A.rooted x k w).width_unit _)) (ne_top_of_le_ne_top (ht.cost w (he w)) (quota_mono _ fun _=>(A.rooted x k w).width_unit _))]; abel_nf; rw [add_assoc]
lemma gap_range {Z:Type}{T: Z→ (w:W)→Packet (I w) r}{F:Z→ (w:W)→Packet (J w) r}(l:Finset Z)(h:∀ i∈l,Claim L (A.anchored x u) v (agap A (T i) (F i)))(hh:∀ i∈l,Claim L (A.rooted x k) s (T i))(ht:∀ w,s w≠⊤): Claim L (A.anchored x u) v (agap A (fun w=> ∑ i∈l,T i w) (fun w=>∑ i∈l,F i w)):=by
 convert Claim.sum _ l h using 1; ext1 w; unfold agap; rw [Deck.scroll_sum (A.deck w) _ (fun i hi=> ne_top_of_le_ne_top ((hh i hi).cost w (ht w)) (quota_mono _ fun _=>(A.rooted x k w).width_unit _)),Finset.sum_sub_distrib]
lemma gap_same {T:(w:W)→Packet (I w) r}{F:(w:W)→Packet (J w) r} (h:Claim L (A.anchored x u) v (agap A T F))(hh:Claim L (A.rooted x k) s T)(ht:∀ w,s w≠⊤): Claim L (A.anchored x u) v (agap A (fun w=>Packet.symmetry (T w)) (fun w=> Packet.symmetry (F w))):=by
 convert h.robust using 1; ext1 w; unfold agap; rw [Deck.scroll_sym _ (ne_top_of_le_ne_top (hh.cost w (ht w)) (quota_mono _ fun _=>(A.rooted x k w).width_unit _)),symmetry_sub]
end Post
end YM.RegulatorIR.Uniform
