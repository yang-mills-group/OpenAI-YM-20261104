import YM.XSpace.Oscillator

/-!
# First-order bare cost outside many to any free anchor; summation prior to positioning
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Outline
open Function Lattice RG Wilson Source Source.Drops Next.Rank.Normal Contraction Chart2 Finsupp JetGauge Legs MvPolynomial
open scoped Topology BigOperators Classical
variable {G:Gauge}{J Z S:Type*}{R:J→Type*} [∀ i,AddCommGroup (R i)][∀ i,One (R i)] {F:∀ i,Given G (R i)} [AddCommGroup S][One S]
-- arity along Z used only in maps op
abbrev Arithmetic (R:J→Type*)(Z:Type*) := ∀ i:J,(Z→Four (R i))→ Four (R i) → ℂ
def Toll (F:∀ i:J, Given G (R i))(p:Arithmetic R Z): Prop := ∃ C:ℝ,0≤C∧∀ i m (x: Z → Four (R i))(s:Finset (Four (R i))), (∀ y∈s,∀ j,(F i).goal m (x j) y)→∑ w∈s,‖p i x w‖ ≤ C * saving m
namespace Toll
variable {p q: Arithmetic R Z} {V:Type*}
lemma add (h:Toll F p)(g:Toll F q): Toll F (fun j x y=>p j x y+q j x y):=by
  obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,K⟩:=g; refine ⟨C+D,by positivity,fun i m x s hs=>?_⟩; apply le_trans (Finset.sum_le_sum fun y hy=> norm_add_le _ _); rw [Finset.sum_add_distrib,add_mul]; exact add_le_add (H _ _ _ _ hs) (K _ _ _ _ hs)
lemma shift (h:Toll F p)(z:ℂ): Toll F (fun i x y=> z*p i x y):=by obtain ⟨C,hC,H⟩:=h; refine ⟨‖z‖*C,by positivity,fun i m x s hs=>?_⟩; simp_rw [norm_mul,← Finset.mul_sum,mul_assoc]; exact mul_le_mul_of_nonneg_left (H _ _ _ _ hs) (norm_nonneg _)
lemma negative (h:Toll F p): Toll F (fun i x y=> -p i x y):=by simpa using h.shift (-1)
lemma sub (h:Toll F p)(g:Toll F q): Toll F (fun i x y=>p i x y - q i x y):=by simpa only [sub_eq_add_neg] using h.add g.negative
lemma zero : Toll F (Z:=Z) (fun _ _ _=>0):=⟨0,by simp,by intros; simp⟩
lemma sum (s:Finset V)(p:V→Arithmetic R Z)(h:∀ i∈s,Toll F (p i)): Toll F (fun i x y=> ∑ j∈s,p j i x y):=by
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact zero
  | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=> h j (by simp [hj]))
lemma with_cost {q : ∀ i:J,(Z→Four (R i))→ℂ} (h:Toll F p)(hc: Quotation (R:=R) q): Toll F (fun i x y=>p i x y*q i x):= by
  obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,K⟩:=hc; refine ⟨D*C,by positivity,fun i m x s hs=>?_⟩; rw [mul_assoc]; apply le_trans _ (mul_le_mul_of_nonneg_left (H _ _ _ _ hs) hD.le); rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro y _; rw [norm_mul,mul_comm]; exact mul_le_mul_of_nonneg_right (K _ _) (norm_nonneg _)
end Toll

variable (h: Society F)
def warp (F:∀ i:J,Given G (R i))(j:Z × Wing G ℤ) (k:Bone G ℤ): Arithmetic R Z:=fun i x y=> (F i).reacts j.2 k (x j.1) y
include h in
lemma cap_three (a b c: Z × Wing G ℤ) (u v w: Bone G ℤ): Toll F (fun i x y=> warp F a u i x y*warp F b v i x y*warp F c w i x y):= by
  obtain ⟨C,hC,H⟩:= h.single a.2 u; obtain ⟨D,hD,K⟩:= h.energy b.2 v; obtain ⟨V,hV,A⟩:= h.energy c.2 w; refine ⟨C*(D+V),by positivity, fun i m x s hs =>?_⟩
  let f:= warp F b v i x; let g:=warp F c w i x
  calc _ ≤ ∑ y∈s,(C*saving m)*(‖f y‖^2+ ‖g y‖^2):= ?_
       _ = C*saving m*((∑ y∈s,‖f y‖^2)+∑ y∈s,‖g y‖^2) := by rw [← Finset.mul_sum,Finset.sum_add_distrib];
       _ ≤ _:= by rw [mul_right_comm C (saving m)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (K i (x b.1) s) (A i (x c.1) s)) hC.le) (saving_ok _).le
  apply Finset.sum_le_sum; intro y hy; rw [norm_mul,norm_mul,mul_assoc]; change ‖_‖*(‖f y‖*‖g y‖) ≤ _; exact mul_le_mul (H _ _ _ _ (hs y hy _)) (by nlinarith [sq_nonneg (‖f y‖- ‖g y‖),sq_nonneg ‖f y‖,sq_nonneg ‖g y‖]) (by positivity) (mul_nonneg hC.le (saving_ok _).le)

-- multiply and average

def gust (V:St ℤ G)(p:Music)(g:Given G S)(x:Z→Four S)(y:Four S):= blend g.grant 0 ((g.points y).pull V*shroud g x p)

private lemma threeFactors {U:Type*}(c:JetGauge.Cov U)(i j k:U)(P:poly U)(h:c.cov i j=0)(p:c.cov i k=0)(q:c.cov j k=0): blend c 0 (X i*X j*X k*P)=blend c 0 (slit (c.cov k) (slit (c.cov j) (slit (c.cov i) P))):=by rw [mul_assoc,mul_assoc,blended]; simp only [slit_prod,h,p,map_zero,zero_mul, add_zero,Pi.zero_apply,zero_add]; rw [blended]; simp only [slit_prod,q,map_zero,zero_mul,add_zero,Pi.zero_apply,zero_add]; rw [blended]; simp
lemma warp_slit (g:Given G S)(x:Z→Four S)(y)(f:Bone G ℤ)(K:Music) : slit (g.grant.cov (g.burn y f)) (shroud g x K)= shroud g x (∑ i∈K.vars, g.reacts i.2 f (x i.1) y • δ i K):=by
  rw [shroud, exchange_slit,split_sum _ K.vars K.mem_supported_vars]; rfl
include h in
lemma toll_gust (p:Music (Z:=Z) (G:=G))(i j k:Bone G ℤ)(e:i.2≠j.2)(f:i.2≠k.2)(g:j.2≠k.2): Toll F (fun l x y=> gust (X i*X j*X k) p (F l) x y):=by
  have he (l:J)(x:Z→Four (R l))(y:Four (R l)): gust (X i*X j*X k) p (F l) x y=∑ a∈p.vars,∑ b∈(δ a p).vars, ∑ c∈(δ b (δ a p)).vars,
      warp F a i l x y*warp F b j l x y*warp F c k l x y*blend (F l).grant 0 (shroud (F l) x (δ c (δ b (δ a p)))):=by
    unfold gust Chart.pull; simp only [map_mul,rename_X]; change blend _ _ (X ((F l).burn y i)*_*_*_)=_
    let M:= (F l).grant; rw [threeFactors M ((F l).burn y i) ((F l).burn y j) ((F l).burn y k) _ (h.color l _ _ e) (h.color l _ _ f) (h.color l _ _ g)]
    unfold M; simp only [warp_slit,map_sum,map_smul, Derivation.map_smul,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; simp only [smul_eq_mul,mul_assoc,warp]
  simp_rw [he]; refine Toll.sum _ _ (fun a _=> Toll.sum _ _ (fun b _=> Toll.sum _ _ fun c _=>(cap_three h a b c i j k).with_cost ?_)); simp_rw [← operate]; apply estimate _ h
lemma pull_C (g:Chart ℤ S)(x:ℂ): g.pull (C x)= (C x: St S G):= by simp [Chart.pull]
include h in
set_option maxHeartbeats 800000 in
theorem toll_integrals (p:Music (Z:=Z) (G:=G))(o:PlaqAxes): Toll F (fun l x y=> blend (F l).grant 0 (V3 G (y,o)*shroud (F l) x p)):=by
  have he : ∀ l x y,gust (V3 G ((0:Cover),o)) p (F l) x y=blend (F l).grant 0 (V3 G (y,o)*shroud (F l) x p):=by intro l x y; simp only [gust, Chart.v3, Given.gone]
  have hp (v:ℂ)(P): Toll F (fun l x y=> gust P p (F l) x y) → Toll F (fun l x y=> gust (C v*P) p (F l) x y):=by
    intro h; have H (l:J)(x:Z→Four (R l))(y:Four (R l)): gust (C v*P) p (F l) x y=v*gust P p (F l) x y:=by unfold gust; rw [map_mul (Given.points (F l) y).pull,pull_C,mul_assoc,C_mul',map_smul]; rfl
    simp_rw [H]; exact h.shift _
  let P:Face ℤ:=(0,o); let T(u:St ℤ G)(v w:Bone G ℤ):=u * X v * X w
  simp_rw [← he]; change Toll F (fun l x y=> gust (V3 G P) _ _ _ _)
  have hg {α:Type}(s:Finset α)(f:α→St ℤ G): (∀ a∈s,Toll F (fun l x y=> gust (f a) p (F l) x y)) → Toll F (fun l x y=> gust (∑ i∈s,f i) p (F l) x y):=by
    intro h; have hx (l x y): gust (∑ i∈s,f i) p (F l) x y=∑ i∈s,gust (f i) p (F l) x y:=by unfold gust; simp only [map_sum,Finset.sum_mul]
    simp_rw [hx]; exact Toll.sum s (fun i l x y=> gust (f i) p (F l) x y) h
  rw [v_as_sum]; apply hg; intro v _; apply hg; intro i _; apply hg; intro j _; apply hg; intro k _
  by_cases h': i=j∨j=k∨i=k
  · simp_rw [v_off i j k h']; simpa [gust] using Toll.zero (F:=F) (Z:=Z)
  push Not at h'; obtain ⟨e,u,w⟩:= h'; apply hp
  set a:Bone G ℤ:=(v.1,j); set b:Bone G ℤ:=(v.2,k)
  let G' (z:St ℤ G) := fun (l:J)(x:Z→Four (R l))(y:Four (R l))=> gust (T z a b) p (F l) x y
  have hs (z r:St ℤ G) : G' (z+r)=fun i x y=> G' z i x y+ G' r i x y:=by simp only [G',gust,T,add_mul,map_add]
  have hn (z r:St ℤ G) : G' (z-r)=fun i x y=> G' z i x y- G' r i x y:=by simp only [G',gust,T,sub_mul,map_sub]
  have hk (z:Edges2 ℤ): Toll F (G' (glyph (single (z,i) 1))):=by rw [glyph,linearCombination_single,one_smul]; exact toll_gust h p (z,i) a b e w u
  change Toll F (G' (glyph _)); simp only [ringBell,map_add,map_sub,hn,hs]; exact (((hk _).add (hk _)).sub (hk _)).sub (hk _)
end YM.XSpace.Outline
