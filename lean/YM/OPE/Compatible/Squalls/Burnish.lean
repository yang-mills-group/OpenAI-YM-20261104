import YM.OPE.Compatible.Squalls.Char
/-! # Polynomial moment equality universality. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics WardBin
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable [Fintype I]{x:I→fieldX (Shade G)} {k:I→ℕ}{R:PathData G}{p:Clip}
lemma sullen {P:ℕ→ Atom G n} (hx:n ≥3)(h: SumBudget (fun j=> (P j).budget s) U) (hs:0<s)(he:radiantX x k) (v:Signed)(hg:d≤4):summitX (paymentAtoms P v) x k d=0:=by
   have H:= accompaniment (smelt_cost h hs v) (fun j a u=>brightD ..) (div_pos hs (by norm_num)) (lumenD G) x k (fun i=>low_quiet (he i)) d
   apply tendsto_nhds_unique H; have hz(i:ℕ×Cue G n): leading d (fun t:ℝ=> verseX (smelt P v i) (lotU (spout x k t)))=0:=by
       apply Eq.trans (spinShot he ((P i.1).leg) v i.2 (by omega : d ≤ n*2)); exact if_neg (by omega)
   change HasSum _ _; simp_rw [hz];simp [hasSum_zero]
lemma singBlank (hx:radiantX x k)(h:R.Bounds p s b U)(hg:d ≤4)(v:Signed):summitX (paymentAtoms R.loop v) x k d=0:=by
   have H := accompaniment (smelt_cost h.two h.width v) (fun j a u=>brightD ..) (div_pos h.width (by norm_num)) (lumenD G) x k (fun i=>low_quiet (hx i)) d
   rw [← H.tsum_eq,H.summable.tsum_prod]; let f:=fun (i:ℕ) (q:Cue G 2)=> leading d (fun t:ℝ=> verseX (smelt R.loop v (i,q)) (lotU (spout x k t))); let y(i:ℕ)(q:Cue G 2):=brass R.loop (i,q)*f i q
   have hh: Summable (uncurry y):=H.summable; change (∑' i:ℕ,∑' j:Cue G 2,y i j)=_; rw [← hh.tsum_comm,tsum_fintype]; refine sum_eq_zero fun i _=>?_ ; let B(j:ℕ) :Fin 2→PlaqAxes:= fun x=> ((R.loop j).leg x).plaq; let F(k':Fin 2→PlaqAxes):ℝ:= if d=2*2 then ∏ j,CurlX x k v (k' j) (i j) else 0
   have hp (b:ℕ) : y b i=(R.loop b).coeff i * F (B b):=by unfold y brass f; congr 1; exact spinShot hx ((R.loop b).leg) v i hg
   rw [← Sack.anchor_sum B (f:=fun b=>y b i) ((hh.prod_symm).prod_factor i)]
   rw [tsum_fintype]; apply sum_eq_zero; intro j _; rw [show Sack.rope B (fun j=> y j i) j= (∑' b,R.loop_coeff j i b)* F j from ?_, (h.loop_normal j i).1,zero_mul]
   rw [← tsum_mul_right]; unfold Sack.rope; apply tsum_congr; intro b; by_cases H:B b=j; · rw [if_pos H]; dsimp only; rw [hp,H]; change _ = (if B b = j then _ else _) * _; rw [if_pos H]
   rw [if_neg H]; change _= (if B b=j then _ else 0) * F j; rw [if_neg H,zero_mul]
-- aggregate
lemma wage_paid (G:Gauge)(p:Clip)(s b:ℝ)(hs:0<s)(m n:ℕ):∃ y:ℝ,∀ R:PathData G,∀ U,R.Bounds p s b U→∀ v t,soot n (waistX R p v t m) y:=by
   obtain ⟨A,ha,H⟩ := totalBudget (I:=Unit) G n m 1 _ _ hs (lumenD G); obtain ⟨C,hc,g⟩:= totalBudget (I:=ℕ×ℕ) G n m 2 (s/2) _ (div_pos hs (by norm_num)) (lumenD G)
   exact ⟨_,fun R U h v t=> (Sack.scale_line (H _ _ _ (ledgerF t v G s) (fun _ _=>litD t v)) p.direct).splits (Sack.scale_line (Sack.finGather _ _ _ (fun i _=>g _ _ (b*b) (duet_cost h v t i) (duet_funds R v t i)) (fun i=>zero_le_one.trans (payer n _))) (1/2:ℝ)) (fun i=>zero_le_one.trans (payer n i))⟩
lemma toneSum (h:R.metric_zero p)(v:PlaqAxes→G.Color): p.direct*(∑ i, ‖v i‖^2)+(∑ i, ‖reachesQ R v i‖^2)=(∑ i,‖v i‖^2):=by
   simp_rw [← real_inner_self_eq_norm_sq]; let P:=p.direct
   have he(i):inner ℝ (reachesQ R v i) (reachesQ R v i)=∑ j, ∑ a, R.symbol0 i j * R.symbol0 i a * inner ℝ (v j) (v a):=by simp_rw [reachesQ,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,← mul_assoc]
   let A(i j a):=R.symbol0 i j * R.symbol0 i a* inner ℝ (v j) (v a); have ht : (∑ i: PlaqAxes,∑ j,∑ a,A i j a)= ∑ j,∑ a,∑ i,A i j a:=by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
   rw [mul_sum]; simp_rw [he]; rw [ht, ← sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; unfold A; simp_rw [← sum_mul, show ∀ a,(∑ k,R.symbol0 k i*R.symbol0 k a)= (if i=a then 1 else 0)-if i=a then P else 0 from fun a=>by have := h i a; rw [← this]; abel] --
   rw [sum_eq_single i]; simp only [P,if_true];ring
   · intro j _ hj; rw [if_neg hj.symm,if_neg hj.symm,sub_self,zero_mul]
   simp
end Script
end YM.OPE.Flume
