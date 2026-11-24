import YM.OPE.Compatible.Tony.Dole
/-!
# Exposing measurements in weighted suit
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script.Wool
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J X Y:Type}{d m r k i:ℕ}{G:Gauge}
variable {a b s t q K σ C D:ℝ}
open Page Merchant Variance
variable {n:Side}
private lemma Xpower (d k:ℕ)(s:ℝ)(he:0<s):∃ A:ℝ,0 ≤ A∧∀ i:ℕ, (k+1+2*i:ℝ)^d ≤ A* Real.exp (s*i):=by
        let U:= (d.factorial:ℝ); let C:ℝ:= ↑k+1; have hc:0<C:=(by unfold C; positivity); let a:=s/2; have ha:0<a:=half_pos he; have hb:0<U:=by unfold U; positivity
        refine ⟨(a^d)⁻¹*U*Real.exp (a*C),mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha.le _)) hb.le) (Real.exp_nonneg _),fun i=>?_⟩; change (C+2*i)^d ≤ _; let x:=C+2*i; have hx:0 ≤ x:=by unfold x; positivity
        have hA:= Real.pow_div_factorial_le_exp (a*x) (mul_nonneg ha.le hx) d; calc
             _ = (a^d)⁻¹*U*((a*x)^d/U):=by change x^d=_; rw [mul_pow]; field_simp
             _ ≤ (a^d)⁻¹*U*Real.exp (a*x):=mul_le_mul_of_nonneg_left hA (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha.le d)) hb.le)
             _ = _:=by rw [mul_assoc ((a^d)⁻¹*U),← Real.exp_add]; apply congr_arg;unfold x a; ring_nf
structure choir (M:ℕ)(p q:deck I n):Prop where
        bank :∀ i,pdist i.1≤ M→p i=q i
lemma Harmony (x:Site n)(v:deck I n)(p q:Fin r→deck I n)(h:∀ i,choir m (p i) (q i))(i:Page I (r+1))(hx:pdist x+2*stamp i ≤ m):
        render (glowK i x) i (Fin.cons v p)= render (glowK i x) i (Fin.cons v q):=by unfold render; rw[Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_zero]; apply congr_arg; exact prod_congr rfl fun j _=>by rw[Fin.cons_succ,Fin.cons_succ]; exact (h j).bank _ ((temperP j.succ i x).trans hx)
variable [Fintype I]
private lemma spree {I:Type} {F:I→ℝ} {U:ℝ}{g:I→ℝ}{u c:ℝ}(ht:Sack F g u) (p:I→ℝ)(he:HasSum p U)(hp:∀ i, ‖p i‖≤c*(F i*‖g i‖))(hc:0≤c): ‖U‖ ≤ c*u:=by
       rw [← he.tsum_eq]; apply (norm_tsum_le_tsum_norm he.summable.norm).trans; apply (he.summable.norm.tsum_le_tsum hp (ht.2.1.mul_left c)).trans; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ht.2.2 hc
lemma Plenty (k m:ℕ)(a:ℝ)(h:0<a):∃ C:ℝ,0 ≤ C ∧∀ (n:Side)(x:Site n)(P:Script I (k+1))(s:ℝ), Felt P a s→ pdist x ≤ m→∀ (p:Fin k→deck I n)(v:deck I n) (b d:ℝ),0 ≤ b→ 0 ≤ d→ BoundsE v x b→ (∀ j,Revenue d (p j))→ ‖library n P (Fin.cons v p)‖≤ C*b*d^k*s:=by
       obtain ⟨C,hc,H⟩:=Xpower k m a h; refine ⟨C,hc,fun n x P s hs hm p v b d hb hd hv hp=>?_⟩; apply spree hs _ (scroll P x p v hv (Sack.water hs (fun _=>sorgh _ h.le))) ?_ (by positivity); intro i; rw [norm_mul]; let t:=stamp i; have he : costume x ≤ (m+1:ℝ):=by unfold costume; rw [add_comm];gcongr
       have ht:‖render (glowK i x) i (Fin.cons v p)‖ ≤ b*d^k *salt a i*C:=by
            have hh:0 ≤ costume x:= (tensile _).le; apply (Major i x p hv hp hd).trans; rw [mul_pow]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) (add_le_add_left he _) _).trans (H t)) (pow_nonneg hd k)) hb).trans_eq; unfold salt;unfold t; ring
       exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by ring)
lemma Altitude (k m:ℕ)(a:ℝ)(h:0<a):∃ C:ℝ,0 ≤ C ∧∀ (n:Side)(x:Site n)(P:Script I (k+1))(s:ℝ)(N:ℕ), Felt P a s→ pdist x ≤ m→∀ (p q:Fin k→deck I n)(v:deck I n) (b d:ℝ),0 ≤ b→ 0 ≤ d→ BoundsE v x b→ (∀ j,Revenue d (p j))→ (∀ j,Revenue d (q j))→(∀ j,choir N (p j) (q j))→ ‖library n P (Fin.cons v p)-library n P (Fin.cons v q)‖≤ C*b*d^k*Real.exp (-(a/4)*(N:ℝ))*s:=by
       obtain ⟨C,hc,H⟩:=Xpower k m (a/2) (half_pos h); let Z:=2*C*Real.exp ((a/4)*m); refine ⟨Z,mul_nonneg (mul_nonneg (by norm_num) hc) (Real.exp_nonneg _),fun n x P s N hs hm p q v b d hb hd hv hp hq hy=>?_⟩; have huq:0 ≤ Z:=mul_nonneg (mul_nonneg (by norm_num) hc) (Real.exp_nonneg _); have hP :=Sack.water hs (fun _=>sorgh _ h.le); let U:=scroll P x p v hv hP; let V:=scroll P x q v hv hP
       refine spree hs _ (U.sub V) (fun i=>?_) (by positivity); by_cases h_:pdist x+2*stamp i≤ N; · rw [Harmony x v p q hy i h_,sub_self,norm_zero]; have hz:=Real.exp_nonneg (a*stamp i); unfold salt; positivity
       let l(i:ℕ):ℝ:=i; have hh:0 ≤ costume x:= (tensile _).le; have he: costume x ≤ (m+1:ℝ):=by unfold costume; rw[add_comm];gcongr
       let f(g:Fin k→deck I n):= render (glowK i x) i (Fin.cons v g); let t:=stamp i; let u:=salt (a/2) i; have hx(g:Fin k→deck I n)(h:∀ i,Revenue d (g i)): ‖f g‖ ≤ b*d^k*u*C:=by
            apply (Major i x g hv h hd).trans; rw [mul_pow]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity) (add_le_add_left he _) _).trans (H t)) (pow_nonneg hd k)) hb).trans_eq; unfold t u salt; ring
       change ‖P i*f p-P i*f q‖≤_; let W:= Z*Real.exp (-(a/4)*(N:ℝ))*salt a i; have ht : 2*(u*C) ≤ W:=by
            have hz:0 ≤ b:=hb; have hL:(N:ℝ) ≤ m+2*t:=by exact_mod_cast (show N ≤ m+2*t by unfold t;omega)
            have hv : a/2*t ≤ a/4*m + -(a/4)*N + a*t:= (by nlinarith [mul_le_mul_of_nonneg_left hL h.le]); have hw:= Real.exp_monotone hv; rw [Real.exp_add, Real.exp_add] at hw; unfold W Z; rw[mul_assoc (2*C),mul_assoc (2*C)]; exact (show 2*(u*C)= 2*C*u from by ring).trans_le (mul_le_mul_of_nonneg_left hw (by positivity))
       apply (norm_sub_le ..).trans; rw [norm_mul,norm_mul]; apply (add_le_add (mul_le_mul_of_nonneg_left (hx p hp) (norm_nonneg _)) (mul_le_mul_of_nonneg_left (hx q hq) (norm_nonneg _))).trans; calc
              _= (‖P i‖*(b*d^k))*(2*(u*C)):=by ring
              _ ≤ (‖P i‖*(b*d^k))*W:=mul_le_mul_of_nonneg_left ht (by positivity)
              _ =_:=by unfold W; ring
end YM.OPE.Flume.Script.Wool
