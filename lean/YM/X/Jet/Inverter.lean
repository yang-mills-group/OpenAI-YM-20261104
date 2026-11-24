import YM.X.Jet.Sparkle
/-!
# Two-sided formal inverses for unit parameters. Uniqueness. using analytic local inverses on arbitrarily high but *finite* truncations and jet uniqueness. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Jet
open Function Filter Set
open scoped Topology ContDiff BigOperators Classical
variable {n m :ℕ} {V:Type*}
local notation "E"=>Word ℝ
variable {a b c:E}
abbrev Genuine (x:E):Prop:=light x∧ x 1≠0
structure PairK (n:ℕ)(a b:E) : Prop where
    starts : light a
    live : light b
    L : fitto (ren a b) headway n
    R : fitto (ren b a) headway n
private lemma certified (h:Genuine a)(n:ℕ):∃ b:E, PairK n a b:= by
    let N:=n+1; let f:=delay a N; have hf': Act N f a:= Act.swell _ le_rfl; have hf : AnalyticAt ℝ f 0:= hf'.nice.analyticAt; have hf₀:f 0=0:=hf'.zero.trans h.1
    have he: deriv f 0 ≠ 0:= by rw [(hf'.first (by omega)).deriv]; exact h.2
    let g:=hf.hasStrictDerivAt.localInverse _ _ _ he; have hg: ContDiffAt ℝ ω g 0:= by rw [← hf₀]; exact (hf.analyticAt_localInverse he).contDiffAt
    have hk: g ∘ f =ᶠ[𝓝 0] id := HasStrictDerivAt.eventually_left_inverse hf.hasStrictDerivAt he
    have hg0 : light (someJ g):= by rw [light, someJ_zero]; (nth_rw 1 [← hf₀]); exact hk.self_of_nhds
    have hl: f ∘ g =ᶠ[𝓝 0] id := by rw [← hf₀]; exact HasStrictDerivAt.eventually_right_inverse hf.hasStrictDerivAt he
    have hp:= eo_Act n hg; have ht:= hf'.shrink (Nat.le_succ n); refine ⟨someJ g,h.1,hg0, fun i hi=> ((ht.dial hp h.1).realizes hk).trans_at (Act.headway _) hi,fun i hi=> ((hp.dial ht hg0).realizes hl).trans_at (Act.headway _) hi⟩
lemma fitto_shrink {p q:Word V}(h:fitto p q n)(hp:m≤n):fitto p q m:= fun _ he=> h _ (he.trans hp)
lemma PairK.shrink (h:PairK n a b)(hp:m≤n):PairK m a b:= ⟨h.starts,h.live,fitto_shrink h.L hp, fitto_shrink h.R hp⟩
lemma PairK.right (h:PairK n a b)(hh:light c)(ht:fitto (ren c a) headway n) : fitto c b n:= by
   intro i hi; calc
    _ =ren c headway i:= (congr_fun (head_ren hh) _).symm
    _ = ren c (ren a b) i:=(price_p h.L (fun j _=>rfl) i hi).symm
    _ = ren (ren c a) b i:= congr_fun (asc hh h.starts _) _
    _ = ren headway b i:= price_p (fun j _=>rfl) ht i hi
    _ = _:= congr_fun (ren_head b) _
def inverse (p:E): E:= if h:Genuine p then (fun i=>(certified h i).choose i) else headway
lemma repar (p:E)(h:Genuine p)(n:ℕ):PairK n p (inverse p):= by
    let b(n):=(certified h n).choose; have he(k):PairK k p (b k):=(certified h k).choose_spec; let a:=inverse p; have ht : fitto a (b n) n:= fun i hi=> by unfold a inverse; rw [dif_pos h]; exact (PairK.right ((he n).shrink hi) (he i).live (he i).R) i le_rfl
    refine ⟨h.1, (ht 0 (Nat.zero_le n)).trans (he n).live, fun i hi=> (price_p ht (fun i _=>rfl) i hi).trans ((he n).L i hi), fun i hi=> (price_p (fun i _=>rfl) ht i hi).trans ((he n).R i hi) ⟩
@[simp] lemma lives (a:E): light (inverse a):= by by_cases h:Genuine a; exact (repar a h 0).live; simpa only [inverse,dif_neg h] using head_light
lemma guarded (h:Genuine a) : ren (inverse a) a=headway:= funext fun i=>(repar a h i).R i le_rfl
lemma headback (h:Genuine a): ren a (inverse a)=headway:= funext fun i=>(repar a h i).L i le_rfl
lemma tip_inv (h:Genuine a): inverse a 1=(a 1)⁻¹:= by have he:=congr_fun (guarded h) 1; rw [tip_head,tip (lives a),smul_eq_mul] at he; exact eq_inv_of_mul_eq_one_left he -- name
lemma invert_odd (h:Genuine a)(he:turn a= -a): turn (inverse a)= - inverse a:= by
    let c:= inverse a; let b:=turn c; apply neg_injective; rw [neg_neg]; change -b=c; have hb: light b:= (turn_zero _).trans (lives ..); let d:=-b; have hd:light d:= (show d 0= -(0:ℝ) from congr_arg Neg.neg hb).trans neg_zero -- name
    have ht: ren d a=headway:= by
       have hx:= congr_arg (ren b) he; rw [ren_turn_v _ hb, show (ren b (-a))= - (ren b a) from ?_] at hx
       · rw [show ren d a= _ from hx, ren_turn_x (x:=c) _ (lives ..), show ren c a=headway from guarded h]; let f:= id (α:=ℝ); have he: turn headway=-headway:= by
            funext i;  have hx := Act.headway i; have hp:= hx.reflects; have hh: Act i (fun x:ℝ=> -x) (-headway) := by simpa using! hx.smul (-1)
            exact hp.trans_at hh le_rfl
         exact (congr_arg Neg.neg he).trans (neg_neg _)
       funext i;unfold ren order; simp only [Pi.neg_apply,smul_neg,Finset.sum_neg_distrib]
    funext i; exact ((repar a h i).right hd (fun k _=>congr_fun ht k) i le_rfl)
end YM.PositionX.Jet
