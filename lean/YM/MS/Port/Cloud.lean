import YM.MS.Vane.Trigger
/-!
# Change clock from µ-exp-σ to µ by scaling positions (i.e functions native heat from physical heat)
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Port
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo Vane
open Osc Fiddle Snap Book.Convolve Alps Arts City
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{F H:Law G}{K:Edge G}{u:ℕ}
abbrev Ψ (G:Gauge):= PlanetD G
abbrev τ (u:ℤ)(s:ℝ): ℂ:= ((exp s ^ u:ℝ):ℂ)
lemma τ_amt (u:ℤ)(s:ℝ): amount (u:ℂ) s=τ u s:= by rw [← Complex.ofReal_intCast, amount_mint]; unfold τ; rw [ a_e,mul_comm ]
lemma T_add (u v:ℤ)(s:ℝ): τ u s*τ v s=τ (u+v) s:= by simp only [ ← τ_amt, Int.cast_add, amount_add ]
lemma disperse (F:QP→ℂ)(s:ℝ): ∫ i, F ( rexp s • i ) ∂planeF=τ (-4) s * ∫ i,F i ∂planeF:= by
    rw [Measure.integral_comp_smul_of_nonneg _ F (hR:=(exp_pos s).le), show Module.finrank ℝ QP=4 from (by simp [QP,Momentum,Axis])]; unfold τ; congr 1; -- inspect z pow
lemma figure (t s:ℝ)(i j:BH G)(p:QP): Ψ G t i j p=τ ( (4:ℤ)-wfield i-wfield j ) s* Ψ G (t-s) i j ( exp s • p ):= by
    unfold Ψ; rw [ planetEra i j t, planetEra i j (t-s) ]; unfold τ era; let r:ℤ:=4-wfield i-wfield j; have he:= Real.exp_sub t s; have hp : exp ( t-s )* exp s= exp t:= (eq_div_iff (exp_pos s).ne').mp he; rw [ smul_smul,hp,Complex.real_smul,Complex.real_smul, ← mul_assoc,← Complex.ofReal_mul,← mul_zpow,mul_comm (exp s),hp]
abbrev shift (d:ℤ)(s:ℝ)(F:Law G): Law G:= fun l=> τ (pitch l-d) s*F (sr s l)
lemma trcPort (x s:ℝ)(q:QP)(h:ℤ) (l:Legs (Lane4 G)): trc (Ψ G x) q (shift h s F) l= τ (4+pitch l-h) s*trc (Ψ G (x-s)) (exp s • q) F (sr s l):= by
    have he(i j:BH G): Ψ G x i j q * shift h s F ( (i,q)::(j,-q)::l ) = τ (4+pitch l-h) s * (Ψ G (x-s) i j (exp s • q)*F ((i,exp s • q)::(j,-(exp s • q))::sr s l)):= by
       rw [figure x s]; unfold shift; simp only [sr,List.map_cons, smul_neg]; 
       simp only [pitch,field_cons]; rw [ mul_mul_mul_comm, T_add ]; congr 2; omega
    simp only [at_trc, Finset.mul_sum, he ]
lemma C_port (x s:ℝ)(h:ℤ): cycle (Ψ G x) planeF (shift h s F)=shift h s ( cycle (Ψ G ( x-s )) planeF F ):= by
    ext l; unfold shift; 
    change (∫ q,trc (Ψ G x) q (shift h s F) l ∂planeF)=_
    simp_rw [trcPort x]; rw [integral_const_mul, disperse (fun q=> trc (Ψ G (x-s)) q F (sr s l)) s]; unfold cycle; rw [ ← mul_assoc,T_add ]; congr 2; omega
-- tree direct.Force.A.Weight
lemma totalζ (t:ℝ)(v:Legs (Lane4 G)) (F H: Shared ( Lane4 G ) ℂ)(u:ℂ) (he:∀ l r,Split l r v→F l r=u* H (sr t l) (sr t r)): scatter (field parity) v F= u*scatter (field parity) (sr t v) H:= by
    rw [scatter_sr]; exact Eq.trans (scatter_congr  _ _ _ (u • (fun l r=> H (sr t l) (sr t r))) he) ( map_smul ( allocate _ v ) u _ ) -- inference argument
lemma P_ψ (s:ℝ)(h l u w z a b:ℤ)(H:h+l=u): τ (4-a-b) s*τ (a+h-w) s*τ (b+l-z) s= τ (4+u-w-z) s:= by rw [ T_add,T_add ]; congr 1; omega
lemma χ_front (v t w A B Z P Q R:ℂ)(hp:v*t*w=Z): (v*A)*( B*( t*P)*(w*Q))+R= Z*( A* ( B *P *Q )) + R:= by rw [ ← hp ]; ring
lemma χ (v t w A B Z P Q:ℂ)(hp:v*t*w=Z): (v*A)*( B*( t*P)*(w*Q))=Z*( A*( B*P*Q)):= by rw [← hp]; ring
lemma β_shift (i:Lane4 G)(l:Legs ( Lane4 G ))(p:ℝ)(n:ℤ): shift n p F (i::l)=τ (wfield i.1+pitch l-n) p * F ((i.1,exp p • i.2)::sr p l):= rfl -- field_cons defin reduces? (List.sum); unused q
lemma treesW (t s:ℝ)(h k:ℤ) : tree parity (Ψ G t) (shift h s F) (shift k s H) = shift (h+k-4) s (tree parity (Ψ G (t-s)) F H):= by
    funext l; apply totalζ; intro x y hp; unfold attaches; simp_rw [ net_sr, degree_sr, neg_neg, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [mul_add]; simp_rw [β_shift]; -- simp? rewrite `figure`
    rw [ figure t s, figure t s ]; -- danger repeats
    simp only [ smul_neg ]; have he:= w_mass hp; refine congr_arg₂ (·+·) (χ _ _ _ _ _ _ _ _ ?_) (χ _ _ _ _ _ _ _ _ ?_); rw [P_ψ _ _ _ _ _ _ _ _ he, show 4+pitch l-h-k= pitch l-(h+k-4) from (by omega) ]; rw [show (4:ℤ)-wfield i-wfield j= 4-wfield j-wfield i from sub_right_comm ..,P_ψ _ _ _ _ _ _ _ _ he, show 4+pitch l-h-k=pitch l-(h+k-4) from (by omega) ]
end YM.MS.Port
