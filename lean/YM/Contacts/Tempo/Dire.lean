import YM.Contacts.Tempo.Cover
namespace YM.Contacts.Tempo
open Set Filter Finset
open scoped Topology Classical BigOperators NNReal
noncomputable section
variable {n i j d k:ℕ}{κ:Type}{X:Type}{m:κ→ℕ}{P:κ→ℕ→ℝ→Prop}{b a c u:ℝ}{v g w f:κ→ℕ→ℝ}
def tint (i:ℕ):ℝ:=(1/2:ℝ)^i
lemma tint_glow (i):0< tint i:= by unfold tint; positivity
lemma tint_nil:tint 0=1:= pow_zero _
lemma tint_succ (i:ℕ):tint (i+1)=tint i/2:= by unfold tint; rw [pow_succ]; ring
lemma tint_add (i n): tint (i+n)=tint i*tint n:= pow_add ..
lemma tint_le (i): tint i≤1:= pow_le_one₀ (by exact le_of_lt (by norm_num : (0:ℝ)<1/2)) (by norm_num) -- maybe n
lemma Road.shift (h: Road m P)(hP:Rising P)(j:ℕ): Road m (fun x i=>P x (i+j)):= by obtain ⟨d,b,hb,B⟩:=h; refine ⟨d,b*toll 0 j d,mul_nonneg hb (toll_glow ..).le,fun p i=>hP _ _ _ _ ?_ (B p (i+j))⟩; apply (mul_le_mul_of_nonneg_left (toll_tri _ _ i d) hb).trans_eq ?_; rw [toll_add j i]; ring
def Fog (P:κ→ℕ→ℝ→Prop): κ→ℕ→ℝ→Prop:= fun p i b=> P p i (b*tint i)
def Fade (m:κ→ℕ)(P:κ→ℕ→ℝ→Prop):Prop:= Road m (Fog P)
variable {Q:κ→ℕ→ℝ→Prop}
lemma Rising.fog (h:Rising P):Rising (Fog P):= fun _ _ _ _ he=> h _ _ _ _ (mul_le_mul_of_nonneg_right he (tint_glow ..).le)
lemma Fade.road (h:Fade m P)(hP:Rising P):Road m P:= Road.fall h (fun _ _ _ hb H=> hP _ _ _ _ (mul_le_of_le_one_right hb (tint_le _)) H)
lemma Fade.fall (h: Fade m P)(hx:∀ x i b,0≤b→P x i b→Q x i b): Fade m Q:= Road.fall h (fun _ i _ hb H=> hx _ i _ (mul_nonneg hb (tint_glow ..).le) H)
lemma Fade.up (h:Fade m P)(hx:∀ x i b,0≤b→P x i b→Q x i (c*b))(hc:0≤c):Fade m Q:= by apply Road.up h (c:=c) _ hc; intro x i b hb ht; change Q x i (c*b*tint i); exact (mul_assoc c b (tint i)).symm ▸ (hx x i (b*tint i) (mul_nonneg hb (tint_glow ..).le) ht)
lemma Fade.joint (h:Fade m P)(ht:Fade m Q)(H:Rising P)(U:Rising Q): Fade m (fun p i b=>P p i b∧Q p i b):= Road.joint h ht H.fog U.fog
lemma Fade.many {Y:X→κ→ℕ→ℝ→Prop}(V:Finset X)(h:∀ p∈V,Fade m (Y p))(ht:∀ p∈V,Rising (Y p)):Fade m (fun p i b=>∀ v∈V,Y v p i b):= Road.many (Y:=fun i=>Fog (Y i)) V h (fun p hp=>(ht p hp).fog)
lemma Fade.by_zero (h:Rising P)(hx:∀ p i,P p i 0): Fade m P:= Road.by_zero h.fog fun x i=> by change P x i (0*tint i); rw [zero_mul]; exact hx x i
lemma Fade.shift (h:Fade m P)(hP:Rising P)(j:ℕ):Fade m (fun x i=>P x (i+j)):= Road.fall (Road.shift h hP.fog j) (fun x i b hb H=>hP _ _ _ _ (mul_le_mul_of_nonneg_left ((tint_add i j).trans_le (mul_le_of_le_one_right (tint_glow ..).le (tint_le j))) hb) H) -- lhs b*..; 
variable [NormedAddCommGroup X] {f g w:κ→ℕ→X}
def Shades (m:κ→ℕ)(f:κ→ℕ→X):Prop:= Fade m (fun x i b=> ‖f x i‖≤ b)
namespace Shades
local notation "σ" => Shades m
private lemma normed (f:κ→ℕ→X):Rising (fun x i b=>‖f x i‖≤ b):= fun _ _ _ _ h H=> H.trans h
lemma road (h:σ f):Rates m f:= Fade.road h (normed f)
lemma sun (h:σ f) (j:ℕ):σ (fun x i=> f x (i+j)):= Fade.shift h (normed f) j
lemma neg (h:σ f):σ (fun x i=>-f x i):= Fade.fall h (fun p i b hb H=> by change ‖-f p i‖≤_; rwa [norm_neg])
lemma plus (h:σ f)(hx:σ g):σ (fun p i=>f p i+g p i):= Fade.up (Fade.joint h hx (normed f) (normed g)) (c:=2) (fun p i b hb ht=> (norm_add_le ..).trans ((add_le_add ht.1 ht.2).trans_eq (two_mul ..).symm)) (by positivity)
lemma zero :σ (fun _ _=> (0:X)):= Fade.by_zero (normed _) (fun _ _=> norm_zero.le)
lemma minus (h:σ f)(ht:σ g):σ (fun p i=>f p i-g p i):= by simpa only [sub_eq_add_neg] using h.plus ht.neg
lemma sum {ι:Type}(W:Finset ι){f:ι→κ→ℕ→X}(h:∀ p∈W,σ (f p)):σ (fun p i=> ∑ q∈W,f q p i):= by induction W using Finset.induction with|empty=> simpa only [Finset.sum_empty] using (zero (m:=m) (X:=X))|insert p V hp ih=> simp_rw [Finset.sum_insert hp]; exact (h p (mem_insert_self ..)).plus (ih (fun p he=>h p (mem_insert_of_mem he)))
variable {f g w:κ→ℕ→ℝ}
lemma mul (h:σ f)(ht: Rates m g):σ (fun p i=> f p i*g p i):= by obtain ⟨d,b,hb,B⟩:=h; obtain ⟨j,a,ha,H⟩:=ht; refine ⟨d+j,b*a,mul_nonneg hb ha,fun p i=> ?_⟩; change ‖f p i*g p i‖≤ _*tint i; rw [norm_mul, ← toll_plus]; exact (mul_le_mul (B p i) (H p i) (norm_nonneg _) (mul_nonneg (mul_nonneg hb (toll_glow ..).le) (tint_glow ..).le)).trans_eq (by ring)
lemma flashed (h:σ f): Rates m (fun p i=> f p i/tint i):= by obtain ⟨d,b,hb,H⟩:=h; refine ⟨d,b,hb,fun p i=>?_ ⟩; change ‖f p i/tint i‖≤_; rw [norm_div,Real.norm_of_nonneg (tint_glow i).le,div_le_iff₀ (tint_glow i)]; exact H p i
lemma start (h:Rates m f): σ (fun p i=> f p i*tint i):= Road.fall h (fun p i b _ H=> (show ‖f p i*tint i‖≤ b*tint i from (by rw [norm_mul,Real.norm_of_nonneg (tint_glow i).le]; exact mul_le_mul_of_nonneg_right H (tint_glow ..).le)))
lemma dark (h:σ f)(he:1/2 < c):∃ v, σ v∧Runs c f v:= by
    let F(p:κ)(i:ℕ):= f p i/tint i*2; let g:= gain (2*c) F; obtain ⟨Y,H⟩:= Rates.prices ((h.flashed).mul (g:=fun _ _=>2) (Rates.constant (b:=‖(2:ℝ)‖) (norm_nonneg _) (fun _ _=>le_rfl))) (c:=2*c) (by linarith only [he]); refine ⟨_, start Y,fun p n=>?_⟩; change g p (n+1)*_=c*(g p n*_)+_; let Q:= tint n; have hQ:0<Q:= tint_glow _; rw [show g p (n+1)= (2*c)*g p n+F p n from H p n,tint_succ]; unfold F; change ((2*c)*g p n+f p n/Q*2)*(Q/2)=c*(g p n*Q)+f p n; field_simp
lemma dimming (h:σ f)(hc:1<c)(ht:Rates m g)(hx:Runs c f g):σ g:= by obtain ⟨v,hv,H⟩:= h.dark ((by norm_num : (1:ℝ)/2<1).trans hc); exact (Rates.sole hv.road ht hc H hx) ▸ hv
end Shades
end
end YM.Contacts.Tempo
