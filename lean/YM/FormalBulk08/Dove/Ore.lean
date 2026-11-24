import YM.FormalBulk08.Dove.Port

/-! Convolution absolute before connecting vacuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{P:Page X}{C:Pin P}{θ A:ℝ}
def smoke (θ A:ℝ)(p:ℕ)(x:Leaf P)(n:ℕ):ℝ:= ∑ j∈Finset.range (n+1), ringR (P.mesh x.a) θ x.b (x.b+j)* (A*((P.age x.a).day (x.b+j))^p)
lemma smoke_left (p:ℕ)(x:Leaf P)(n) : smoke θ A p x (n+1)=ringR (P.mesh x.a) θ x.b (x.b+1)*smoke θ A p (stageFoot P x 1) n + A*((chron P).day x)^p:= by
    unfold smoke; rw [Finset.sum_range_succ', Finset.mul_sum]; simp only [add_zero]; rw [show ringR _ θ x.b x.b=1 by simp [ringR,sowing],one_mul];congr 1;apply Finset.sum_congr rfl; intro i _; change _ = ringR (P.mesh x.a) θ x.b (x.b+1) * (ringR (P.mesh x.a) θ (x.b+1) (x.b+1+i)*(A* ((P.age x.a).day (x.b+1+i))^p)); rw [←mul_assoc (ringR (P.mesh x.a) θ x.b (x.b+1)), ring_fee,show x.b+1+i=x.b+(i+1) by omega]
lemma smoke_plus (p:ℕ)(x:Leaf P)(n)(h:0≤A):0≤smoke θ A p x n:= Finset.sum_nonneg fun _ _=> mul_nonneg (Real.exp_pos _).le (mul_nonneg h (pow_nonneg ((P.age x.a).good _) _))
lemma corridor (C:Pin P)(h:Years P)(θ:ℝ)(ht:0<θ)(p:ℕ)(hz:0≤ A): Soft (sage C) (fun x=> smoke θ A p x.toLeaf (C.N x.a - x.b)):= by
    obtain ⟨M,q,m,k,H,Y⟩:= age_leg P h θ ht p
    have hh (n:ℕ): ∑ i∈Finset.range n,q^i≤1/(1-q):= by
       rw [le_div_iff₀ (sub_pos.mpr H),geom_sum_mul_neg]; linarith [pow_nonneg k n]
    have hF:0≤ 1/(1-q):= div_nonneg zero_le_one (by linarith)
    refine ⟨(A*M)*(1/(1-q)),p,by positivity,fun x=>?_⟩; rw [abs_of_nonneg (smoke_plus _ _ _ hz)]
    let n:=C.N x.a-x.b+1; let v:=(sage C).day x; have hv:0≤ v:=(sage C).good x
    have hp:(∑ i∈Finset.range n, ringR (P.mesh x.a) θ x.b (x.b+i)*(A*((P.age x.a).day (x.b+i))^p))≤ ∑ i∈Finset.range n,(A*(M*v^p))*q^i:= by
        apply Finset.sum_le_sum; intro i _; rw [mul_left_comm, mul_assoc]; exact mul_le_mul_of_nonneg_left (Y x.toLeaf i) hz
    apply le_trans hp; rw [← Finset.mul_sum]; refine (mul_le_mul_of_nonneg_left (hh n) (by positivity)).trans_eq ?_; change _= _*v^p;ring
-- abstract induction. Tonic monotonic order costs. top bound only there. Step μ ≤ assumed but not all endpoints
variable {f: Deck C→ℝ→ Prop}
lemma common_heights {A: X→ℝ}{B:Turn C→ℝ}(ha:Soft ((sage C).reach (peak C)) A)(hb:Soft (tide C) B):∃ (W:ℝ)(p:ℕ),0≤W∧(∀ x,A x≤W*((sage C).day (peak C x))^p)∧∀ x,B x ≤ W*((tide C).day x)^p:= by
    obtain ⟨A',n,a,H⟩:= ha; obtain ⟨C',m,c,P'⟩:=hb; refine ⟨A'+C',n+m,add_nonneg a c,fun i=>?_,fun i=>?_⟩
    · refine ((le_abs_self _).trans (H i)).trans ?_; change A'* ((sage C).day _)^n≤ _; exact mul_le_mul (le_add_of_nonneg_right c) (pow_le_pow_right₀ ((sage C).one _) (by omega)) (pow_nonneg ((sage C).good _) _) (add_nonneg a c)
    exact ((le_abs_self _).trans (P' _)).trans (mul_le_mul (le_add_of_nonneg_left a) (pow_le_pow_right₀ ((tide C).one _) (by omega)) (pow_nonneg ((tide C).good _) _) (add_nonneg a c))
lemma upward (h:Years P)(ht:0<θ)(hp:∀ i,∀ a,f i a→∀ b,a≤b → f i b){A:X→ℝ}(he:Soft ((sage C).reach (peak C)) A)(ha:∀ x,f (peak C x) (A x)){B:Turn C→ℝ}(hb:Soft (tide C) B)(hw:∀ x:Turn C,∀ Z,f x.ups Z→0≤Z → f x.bed (Turn.rad θ x*Z+B x)):
     ∃ C':Deck C→ℝ,Soft (sage C) C' ∧ (∀ x,0≤C' x) ∧ ∀ x,f x (C' x) := by
    obtain ⟨W,p,hW,U,H⟩:=common_heights he hb; refine ⟨_,corridor C h θ ht p hW,fun x=> smoke_plus p x.toLeaf _ hW,fun x=>?_⟩
    let y(x:Deck C):=smoke θ W p x.toLeaf (C.N x.a-x.b)
    have hv (n:ℕ) x (e:n+x.b=C.N x.a): f x (y x) := by
       induction n generalizing x with
       | zero=>
         have hd : x.b=C.N x.a:= by rwa [zero_add] at e
         have hx:= hp _ _ (ha x.a) _ (U x.a); rw [show peak C x.a=x by cases x with | mk l m=> rcases l with ⟨a,b,c⟩; simpa [peak] using hd.symm] at hx
         simpa only [y,hd,Nat.sub_self,Nat.zero_add,smoke,Finset.sum_range_one, Nat.add_zero,ringR,sowing,sub_self,mul_zero, Real.exp_zero,one_mul, sage, Time.reach, chron] using hx
       | succ n ih=>
         let v:Turn C:= ⟨x.toLeaf,by omega⟩; have hg: v.ups.b = x.b+1:=rfl; have ht' : v.ups.a=x.a:=rfl; have Hx:=ih v.ups (by rw [hg,ht'];omega); refine hp x _ (hw v _ Hx (smoke_plus _ _ _ hW)) _ ?_ -- elaborate
         unfold y; change ringR (P.mesh x.a) θ x.b (x.b+1) * smoke θ W p _ _ + B v≤ _; rw [show C.N x.a-x.b=n+1 by omega, smoke_left]; rw [show C.N v.ups.a-v.ups.b=n by rw [hg,ht'];omega]; exact add_le_add_right (H v) _
    exact hv _ x (Nat.sub_add_cancel x.cap)
end YM.FormalBulk08.Dove
