import YM.XSpace.Collide

/-!
# Flavor addition when working with arbitrary spatial probes.

Reminder that we can have other variables on BOTH points in the auxiliary matrix once
some factors have been processed. Identities of the multilinear *correlation*, not arbitrary
derivations on our free algebra. Then stabilize arbitrary additional bilocals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Traverse Function Set Filter Finsupp Maxwell Maxwell.Free
open MvPolynomial Next.Rank.Normal
open scoped Topology BigOperators Classical
variable {G : Gauge} (x y : E4) (p q : Flavor 0)
private lemma send_flow (a b : Flavor 0) (e : G.ColorIndex) : (Kf G).cov (lit x (a+b) e)= (Kf G).cov (lit x a e)+(Kf G).cov (lit x b e):=by
  funext i; obtain ⟨y,p⟩:=i
  by_cases h:x=y; subst y; rw [Pi.add_apply]; simp [lit,empty_self]
  let s:= x-y; let L:= (Maxwell.pairing (j:=0) (show s∈away from sub_ne_zero.mpr h)).flip (qr p)
  rw [Pi.add_apply,cash _ _ h,cash _ _ h,cash _ _ h];
  change (L (flavor 0 e (a+b)):ℂ)=(L (flavor 0 e a):ℂ)+(L (flavor 0 e b):ℂ); simp
lemma one_linear (e:G.ColorIndex) (a b : Flavor 0) (P : Pol G) : receive G (X (lit x (a+b) e)*P)=receive G (X (lit x a e)*P)+receive G (X (lit x b e)*P):=by
  simp only [receive,stationed]; unfold first; rw [send_flow,slit_linear,map_add]
lemma bi_linear (a b:Flavor 0) (P: Pol G): receive G (bilocal G (x,a+b) (y,q)*P)=receive G (bilocal G (x,a) (y,q)*P)+ receive G (bilocal G (x,b) (y,q)*P):=by
  unfold bilocal; simp only [Finset.sum_mul,map_sum, mul_assoc,one_linear]; rw [Finset.sum_add_distrib]

variable {x y p q} {S : Finset E4} {v u c : E4}

-- recursive quantifier over spectator tests by LOCAL quadratics
inductive Loc : Nat→ Finset E4→ Pol G →Prop
| stop (S : Finset E4) (P : Pol G) (h : receive G P=0): Loc 0 S P
| sharp (n : ℕ) (S : Finset E4) (P:Pol G) (h : ∀ x p, x∉S→ Loc n (insert x S) (bilocal G (x,p) (x,p)*P)): Loc (n+1) S P

def Silent (S : Finset E4) (P:Pol G) : Prop:=∀ n, Loc n S P
variable {P : Pol G}
lemma Silent.self (K : Silent S P): receive G P=0:=by
  have hh:= K 0; cases hh; assumption
lemma Silent.probe (K : Silent S P) (hx : x∉ S) (p:Flavor 0): Silent (insert x S) (bilocal G (x,p) (x,p)*P):=by
  intro n; have hh:= K (n+1); cases hh with | sharp _ _ _ ht => exact ht _ _ hx
lemma rolling_avoid (H : Wheel v u) (c : E4) (L : Finset E4) : ∀ᶠ t:ℝ in atTop, course c u t∉L:=by
  filter_upwards [show ∀ᶠ t:ℝ in atTop,∀ x∈ L, course c u t≠x from (eventually_all_finset L).mpr (fun x _=> rolling H c x)] with t ht hh; exact ht _ hh rfl

lemma open_path (K : Silent S P) (H : Wheel v u) (hp : P∈Room G S) (A B : Ph) (ha : A.1=c-v) (hb : B.1=c+v)
    (hx : A.1≠B.1) (he : A.1∉S) (hf : B.1∉ S) (hi : ∀ z∈S,jump (interval (c-z) u)≠0)
    (C₀ : G.ColorIndex) (s : Flavor 0) (hs : flash H C₀ s A.2≠0) (ht : flash H.back C₀ s B.2≠0) : receive G (bilocal G A B*P)=0:=by
  have h:=collide s H C₀ P A B ha hb hx hp he hf hi (K.probe he A.2).self (K.probe hf B.2).self
  have hh: Silent _ (bilocal G A A*(bilocal G B B*P)):= ((K.probe hf B.2).probe (show A.1 ∉ insert B.1 S by simp [hx,he]) A.2)
  refine (mul_eq_zero.mp (h.unique ((Traverse.constant _).congr ?_))).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hs) ht)
  filter_upwards [rolling_avoid H c _] with t ht
  rw [quad_play,show receive G _=0 from (hh.probe ht s).self,mul_zero]

private lemma even_dark (B : Flavor 0 →ₗ[ℝ] ℂ) (U : Flavor 0 → ℂ)
    (h : ∃ x:Flavor 0, B x ≠0) (hf : ∀ x, B x≠0 → U x=0) (hi : ∀ x y,U (x+y)=U x+U y) (x:Flavor 0): U x=0:=by
  obtain ⟨y,hy⟩:=h; by_cases he:B x=0; swap; exact hf x he
  apply add_right_cancel (b:=U y); rw [← hi,hf _ (by rw [map_add,he,zero_add]; exact hy),hf y hy,zero_add]

lemma share (K : Silent S P) (e : G.ColorIndex) (hp : P∈Room G S) (x y : Ph) (h : x.1 ≠ y.1) (hx : x.1∉ S) (hy : y.1∉ S): receive G (bilocal G x y*P)=0:=by
  obtain ⟨x,p⟩:=x; obtain ⟨y,q⟩:=y
  let c := (2:ℝ)⁻¹ • (x+y); let v := y-c; have hz : x=c-v:=by unfold v c; module
  have he : y=c+v:=by unfold v; abel
  have hv : v≠0:= fun f=> h (show x=y by simp only [f,sub_zero] at hz; simp only [f,add_zero] at he; exact hz.trans he.symm)
  obtain ⟨u,H,hu⟩:= directions S hv (hz ▸ (show x∉ S from hx)) (he ▸ (show y∉ S from hy))
  obtain ⟨s,ha,hb⟩:= nonsingular H e; let F (p q : Flavor 0):= receive G (bilocal G (x,p) (y,q)*P)
  refine even_dark (flash H e s) (fun p=> F p q) ⟨s,ha⟩ (fun p hp'=>?_ ) (fun _ _=>bi_linear ..) p
  refine even_dark (flash H.back e s) (F p) ⟨s,hb⟩ (fun q => open_path K H hp (x,p) (y,q) hz he h hx hy hu e s hp') (fun a b=> ?_) q
  unfold F; rw [bi_swap (x,p) (y,a+b),bi_swap (x,p) (y,a),bi_swap (x,p) (y,b)]; exact bi_linear ..
lemma Silent.linked (K : Silent S P) (e : G.ColorIndex) (hp : P∈Room G S) (x y : Ph) (h:x.1 ≠ y.1) (hx:x.1∉S) (hy:y.1∉S): Silent (insert x.1 (insert y.1 S)) (bilocal G x y*P) := by
  intro n; induction n generalizing S P with
  | zero=> exact .stop _ _ (share K e hp x y h hx hy)
  | succ n ih=> apply Loc.sharp; intro a p ha
                obtain ⟨hv,hw,ha⟩:= (show a≠x.1 ∧ a≠y.1 ∧ a∉S by simpa using ha)
                have hi := ih (K.probe ha p) (Subalgebra.mul_mem _ (bilocal_on (x:=(a,p)) (h:=Finset.mem_insert_self ..) (y:=(a,p)) (ht:=Finset.mem_insert_self ..)) (room_after a hp)) (by simp [hv.symm,hx]) (by simp [hw.symm,hy])
                rw [mul_left_comm,Finset.insert_comm a x.1,Finset.insert_comm a y.1]; exact hi
end YM.XSpace.Legs
