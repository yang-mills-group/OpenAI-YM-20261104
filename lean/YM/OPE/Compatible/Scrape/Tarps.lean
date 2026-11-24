import YM.OPE.Compatible.Scrape.Bolt
/-!
# Fixed wager, uniform cardinal charges
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Next.Rank Next.Rank.Spindle Source WilsonStartup Gauge Next.Fluctuations Metric Beamer
open MultiNext.SignedSource Lyre Mom Pill
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}
lemma graphP [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup F][NormedSpace ℝ F](f:X→F)(A:E→L[ℝ] X)(x:E)(j:ℕ)(hx:ContDiffAt ℝ j f (A x)) {a b:ℝ}(hv:‖iteratedFDeriv ℝ j f (A x)‖ ≤ a)(he:‖A‖ ≤ b):‖iteratedFDeriv ℝ j (f ∘ A) x‖ ≤ a*b^j:=by
      rw [composeL A f hx]; refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; gcongr; exact (norm_nonneg _).trans hv
lemma grabK [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup X][NormedSpace ℝ X](F:E→X)(j:ℕ)(he:ContDiff ℝ j F)(r:ℝ):∃ C:ℝ,1 ≤ C∧∀ i,i≤j→∀ x:E, ‖x‖≤r → ‖iteratedFDeriv ℝ i F x‖ ≤ C:=by
      letI: ProperSpace E:=FiniteDimensional.proper ℝ _
      choose D H using fun i:Fin (j+1)=> (isCompact_closedBall (0:E) r).exists_bound_of_continuousOn ((he.continuous_iteratedFDeriv (by exact_mod_cast (Nat.le_of_lt_succ i.isLt))).continuousOn)
      let C:=1+∑ i,‖D i‖; have hx:1 ≤ C:= le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>norm_nonneg _); refine ⟨C,hx,fun i hi x h=>?_⟩; let t:Fin (j+1):=⟨i,by omega⟩; exact (H t x (mem_closedBall_zero_iff.mpr h)).trans ((Real.le_norm_self _).trans ((Finset.single_le_sum (f:=fun i=>‖D i‖) (fun i _=>norm_nonneg _) (Finset.mem_univ t)).trans (le_add_of_nonneg_left zero_le_one)))
lemma SpikeY (P:Pad G)(k:ℕ):∃ c:ℝ, 1≤ c∧∀ b:ℕ,∀ x:DrawerB G b,‖x‖≤P.r → ∀ j ≤ k, ‖iteratedFDeriv ℝ j burnU x‖ ≤ c*sizeQ b:=by
     let f(x:G.Color):=‖x‖^2; have hf : ContDiff ℝ k f:= contDiff_id.norm_sq ℝ; obtain ⟨c,hc,h⟩:=grabK f k hf P.r; refine ⟨c,hc,fun b x he j hi=>?_⟩; let q(i:TilesB b):DrawerB G b→L[ℝ] G.Color:=ContinuousLinearMap.proj i; let g:= fun (i:TilesB b)=> f ∘ q i
     rw [show (burnU :DrawerB G b→ℝ)=∑ i,g i from funext fun v=>by rw [Finset.sum_apply];rfl,iteratedFDeriv_sum_apply (n:=j) (f:=g) (fun i _=> ((hf.comp (q i).contDiff).contDiffAt.of_le (Nat.cast_le.mpr hi)))]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>c) (fun i _=>?_)).trans ?_)
     · exact (graphP f (q i) x j (hf.contDiffAt.of_le (Nat.cast_le.mpr hi)) (h j hi _ ((norm_le_pi_norm x i).trans he)) (show ‖q i‖≤1 from (q i).opNorm_le_bound zero_le_one fun v=> (norm_le_pi_norm v i).trans_eq (one_mul _).symm)).trans_eq (by simp)
     simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm (Fintype.card _:ℝ)]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (zero_le_one.trans hc)
abbrev swingG (P:Pad G)(b:ℕ) :DrawerB G b→ℂ:= Complex.ofReal ∘ (fun x=> Swirl P (burnU x))
lemma jumpW (P:Pad G)(k:ℕ):∃ c:ℝ, 0≤c ∧ ∀ b:ℕ,∀ x:DrawerB G b, burnU x ≤ P.r^2→ ‖iteratedFDeriv ℝ k (swingG P b) x‖ ≤ c * sizeQ b ^ k:=by
     let V:ℝ→ℂ:=Complex.ofRealCLM ∘ (Swirl P); have hp: ContDiff ℝ k V:= Complex.ofRealCLM.contDiff.comp (f:=(Swirl P)) (show ContDiff ℝ (k:ℕ∞) (Swirl P) from (Swirl P).contDiff); obtain ⟨D,hD,h⟩:=grabK V k hp (P.r^2); obtain ⟨c,hc,H⟩:= SpikeY P k; refine ⟨k.factorial*D*c^k,(by have hh:=zero_lt_one.trans_le hD; have hz:=zero_lt_one.trans_le hc; positivity),fun b x he=>?_⟩
     have ht:= burnlo x P.pos.le he; refine (strap burnU V x k ((burnsm G b).contDiffAt.of_le le_top) hp.contDiffAt D (c*sizeQ b) (fun i hi=> h _ hi _ ((Real.norm_of_nonneg (burnnn x)).trans_le he)) ?_).trans_eq ?_
     · intro i hy hh; apply (H b x ht i hh).trans; exact (pow_one _).symm.trans_le (pow_le_pow_right₀ (show 1 ≤ c*sizeQ b from one_le_mul_of_one_le_of_one_le hc (by unfold sizeQ; simp)) hy)
     rw [mul_pow,mul_assoc _ (c^k)]
lemma ScrollB (P:Pad G)(k:ℕ):∃ C:ℝ,0≤ C ∧∀ (n:Side)(b:ℕ)(h:2*(b+1)<n.val)(o:Site n)(K:BudgetPoint)(F: Config G n→ℂ)(τ:ℝ)(x:DrawerB G b), ‖x‖≤ P.r→ Widen K b→ k≤ K.order→ K.Regular (Spindle.patch b o) F→ K.supBounds o (Spindle.patch b o) F τ → ‖iteratedFDeriv ℝ k (HeadU o h K F) x‖ ≤ C*τ:=by
     choose C hC H using fun (j:Fin (k+1))=> geV j.val G; choose D hD Q using fun (j:Fin k)=> danceν P (j.val+1) (by omega); let f:= ∑ i,C i; let t:=1+∑ i,D i; have hf:0 ≤ f:= Finset.sum_nonneg fun i _=> zero_le_one.trans (hC _); have ht:1≤ t:=le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> zero_le_one.trans (hD _)); refine ⟨(k.factorial*f*t^k:ℝ), mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hf) (pow_nonneg (zero_le_one.trans ht) _),fun n b h o K F τ x hx hW hg hk hz=>?_⟩
     let L:= K.threshold • ContinuousLinearMap.id ℝ (Directions G n); have hh:= hence o P h K x hx; have hV (i:ℕ)(hi:i ≤ k) : slopeCap i (mill K F) (DanceU o h K x)≤ f*τ:=by
          let j:Fin (k+1):=⟨i,by omega⟩; exact (H j _ o (DanceU o h K x) K b F τ (glaze o P h K x hx) hh hW (hi.trans hg) hk hz).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>zero_le_one.trans (hC i)) (Finset.mem_univ j)) hz.1)
     refine (strap (DanceU o h K) (mill K F) x k ((sob_h o P h K x hx).of_le le_top) (((responsive 1 K hk hh).comp (f:=L) _ L.contDiff.contDiffAt).of_le (Nat.cast_le.mpr hg)) (f*τ) t hV (fun i hi hk=>?_)).trans_eq (by ring); cases i with
     | zero=> omega
     | succ i=> let j:Fin k:=⟨i,by omega⟩; exact (Q j n b K o h x hx).trans ((le_trans (Finset.single_le_sum (fun i _=>zero_le_one.trans (hD i)) (Finset.mem_univ j)) (show _≤ t from le_add_of_nonneg_left zero_le_one)).trans ((pow_one t).symm.trans_le (pow_le_pow_right₀ ht hi))) -- _ ≤ t wildcard
lemma swing_t (P:Pad G) (b k:ℕ):ContDiff ℝ k (swingG P b):=by
     let f:= Complex.ofRealCLM ∘ (Swirl P); have he:ContDiff ℝ k f:=Complex.ofRealCLM.contDiff.comp (Swirl P).contDiff; exact he.comp (f:=burnU) ((burnsm G b).of_le le_top)
lemma lights (P:Pad G)(k:ℕ):∃ C:ℝ,0≤ C ∧∀ (n:Side)(b:ℕ)(h:2*(b+1)<n.val)(o:Site n)(K:BudgetPoint)(F: Config G n→ℂ)(τ:ℝ)(x:DrawerB G b), Widen K b→ k≤ K.order→ K.Regular (Spindle.patch b o) F→ K.supBounds o (Spindle.patch b o) F τ → ‖iteratedFDeriv ℝ k (LaunchB o P h K F) x‖ ≤ C*sizeQ b ^ k *τ:=by
     choose D hD H using fun i:ℕ => jumpW P i; choose f hf hf' using fun i:ℕ=> ScrollB P i; let c(i:ℕ):ℝ := ((k.choose i) :ℝ)*D i* f (k-i); have he(i):0 ≤ c i:=mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD i)) (hf _); let C:= ∑ i∈Finset.range (k+1),c i; have hV:0≤ C:= Finset.sum_nonneg (fun i _=>he i); refine ⟨C,hV,fun n b h o K F τ x hW hk hF ht=>?_⟩
     have hy:1≤ sizeQ b:=le_add_of_nonneg_right (Nat.cast_nonneg _) ; have hΛ:0 ≤ C * sizeQ b ^ k *τ:= mul_nonneg (mul_nonneg hV (pow_nonneg (zero_le_one.trans hy) _)) ht.1; by_cases hx : burnU x ≤ P.r^2
     · have hQ:‖x‖ ≤ P.r:= burnlo x P.pos.le hx; let g:= HeadU o h K F; change slopeCap k (LaunchB o P h K F) x ≤_; rw [show LaunchB o P h K F=(swingG P b)*g from funext fun i=>by change _= ((_:ℝ):ℂ) * _; rw [← Complex.real_smul]; rfl -- edit
           ]; refine (times_slope k ((swing_t P b k).contDiffAt) ((Ch_k o P h K F hF x hQ).of_le (Nat.cast_le.mpr hk))).trans ?_
       unfold C; rw [Finset.sum_mul,Finset.sum_mul]; refine Finset.sum_le_sum fun i hi=>?_;
       have hu:=Finset.mem_range.mp hi; unfold c; let v':ℝ:=k.choose i; have hh:0≤v':=Nat.cast_nonneg _; exact (mul_le_mul (mul_le_mul_of_nonneg_left ((H i b x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (by omega:i≤k)) (hD i))) hh) (hf' _ n b h o K F τ x hQ hW (show k-i ≤ K.order from by omega) hF ht) (norm_nonneg _) (mul_nonneg hh (mul_nonneg (hD i) (pow_nonneg (zero_le_one.trans hy) _)))).trans_eq (by ring)
     have hh:(LaunchB o P h K F)=ᶠ[𝓝 x] (fun _=>0):=by
           let f':= LaunchB o P h K F; filter_upwards [(burnsm G b|>.continuous).continuousAt.eventually (lt_mem_nhds (lt_of_not_ge hx))] with i hi; rw [LaunchB]; rw [show Swirl P (burnU i)=0 from ?_,zero_smul]; by_contra he; have ht: burnU i∈tsupport (Swirl P):= subset_closure (show burnU i∈ support (Swirl P) from he); rw [ContDiffBump.tsupport_eq] at ht; exact not_lt.mpr ((Real.le_norm_self _).trans (mem_closedBall_zero_iff.mp ht)) hi
     rw [(hh.iteratedFDeriv ℝ k).eq_of_nhds,iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]; exact hΛ
end YM.OPE.Spells
