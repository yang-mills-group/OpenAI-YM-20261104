import YM.LocalLTE.Weft.Fabric
import YM.LocalLTE.Fan.Local
/-! Weft projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Set Metric Function MeasureTheory Finset
open Tensor Analysis ConnectedActivityE6.Blaze
open scoped Topology BigOperators Classical ContDiff
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {k n m : ℕ} {f g : ℝ→E} {C:ℝ}
lemma taller (g: E →L[ℝ] F)(f:ℝ→E)(i:J k): pick k (fun s=>g (f s)) i = g (pick k f i):= by unfold pick; rw [map_sum]; simp_rw [map_smul]
omit [NormedAddCommGroup F][NormedSpace ℝ F] in
lemma calcK {v:ℝ→F→E} (A:F)(i:J k): (pick k v i) A= pick k (fun s=> v s A) i:=by unfold pick; rw [Finset.sum_apply]; rfl
lemma caisson {f:ℝ→E}(j:J k)(h:∀ i∈clip, ‖(i^n:ℝ) • f i‖ ≤ C): ‖pick k f j‖ ≤ (∑ i:J k,|slate k i j|/(probe k i)^n)*C:=by
   unfold pick; refine (norm_sum_le ..).trans ?_; rw [Finset.sum_mul]
   refine sum_le_sum fun i _=> ?_
   let x:=probe k i; have he:0<x:=(probes k i).1
   have hv: ‖f x‖ ≤ C/x^n:= (le_div_iff₀ (pow_pos he _)).mpr (by have hF:= h _ (probes k i); rw [norm_smul,norm_pow,Real.norm_of_nonneg he.le,mul_comm (x^n)] at hF; exact hF)
   rw [norm_smul]; exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_eq (by rw [div_mul_eq_mul_div,mul_div_assoc]; rfl)
lemma rotor {j:J k} (hf:Hex k f) {u:ℝ}(hu:u∈clip): pick k (fun i=> f (i*u)) j = mark k j u • pick k f j:=by
   apply picked; intro s hs; have he:0<s:=hs.1
   have hh:s*u∈clip:= ⟨mul_pos he hu.1,mul_le_one₀ hs.2 hu.1.le hu.2⟩
   rw [hf.seen hh]; apply sum_congr rfl; intro i hh; unfold mark; rw [smul_smul,mul_pow,mul_pow,div_mul_div_comm]
lemma vanish (h:Hex k f) (hf:∀ i∈clip, ‖(i^n:ℝ) • f i‖ ≤ C)(j:J k)(he:j.val+n < k): pick k f j=0:=by
   let p:= k-(j.val+n); let g(t:ℝ):= (∑ i:J k, |slate k i j|/(probe k i)^n)*C*t^p; let h':=pick k f j; let L:= (∑ i:J k,|slate k i j|/(probe k i)^n)
   have hz:g 0=0:=by rw [show g 0=L*C*0^p from rfl,zero_pow (by unfold p; omega),mul_zero];
   have HG(g':ℝ)(hg:g'∈clip): ‖h'‖≤ g g':=by
      have hq:= caisson (k:=k) j (f:=fun i=> f (i*g')) (C:=C/(g'^n)) (n:=n) fun i (hh:i∈clip)=>by
         rw [le_div_iff₀ (pow_pos hg.1 _)]; refine le_trans (le_of_eq ?_) (hf (i*g') ⟨mul_pos hh.1 hg.1,mul_le_one₀ hh.2 hg.1.le hg.2⟩); rw [norm_smul,norm_smul,norm_pow,Real.norm_of_nonneg hh.1.le,Real.norm_of_nonneg (pow_nonneg (mul_pos hh.1 hg.1).le _),mul_pow]; ring
      rw [rotor h hg,norm_smul,Real.norm_of_nonneg (show 0 ≤ mark k j g' from div_nonneg (pow_nonneg hg.1.le _) (pow_nonneg hg.1.le _))] at hq
      apply le_of_mul_le_mul_left (a:=mark k j g') (_root_.le_trans hq (?_)) (div_pos (pow_pos hg.1 _) (pow_pos hg.1 _))
      have ht: g'^j.val*g'^p * g'^n=g'^k:=by rw [← pow_add,← pow_add]; congr 1; unfold p; omega
      unfold g mark; have hx := hg.1; field_simp; apply le_of_eq; rw [← ht]; ring
   by_contra hh; have hH:0< ‖h'‖:= norm_pos_iff.mpr hh; have hm : Tendsto g (𝓝[>] 0) (𝓝 (g 0)):= (show Continuous g from (by unfold g; fun_prop)).continuousAt.continuousWithinAt
   obtain ⟨x,H,H',he⟩:=((hm.eventually (gt_mem_nhds (hz.trans_lt hH))).and ((show ∀ᶠ x:ℝ in 𝓝[>] 0,0<x from self_mem_nhdsWithin).and ((eventually_le_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono (nhdsWithin_le_nhds (a:=(0:ℝ)))))).exists; exact H.not_ge (HG _ ⟨H',he⟩)
lemma Hex.smoothWork {f:ℝ→E→F}(h: Hex k f) (he:∀ s∈clip, ContDiffAt ℝ (↑n) (f s) 0) : Hex k (fun s=> Tensor.coeff (f s) n 0):=by
    let c:=pick k f
    have hp i : ContDiffAt ℝ (↑n) (c i) 0:= by unfold c pick; simp_rw [Finset.sum_fn]; exact ContDiffAt.sum fun j _=> (he _ (probes k j)).const_smul (slate k j i)
    refine ⟨fun j=>Tensor.coeff (pick k f j) n 0,fun s hs=> ?_⟩; dsimp only; rw [h.seen hs, Tensor.coeff_sum _ _ _ _ (fun i _=>  (show ContDiffAt ℝ (↑n) (mark k i s • pick k f i) 0 from (hp i).const_smul (mark k i s)))]; exact sum_congr rfl fun i _=> Tensor.coeff_smul _ (hp i)
lemma integralX {Ω:Type} [MeasurableSpace Ω] [CompleteSpace E] {μ:Measure Ω}{f:ℝ→Ω→E} (h:Hex k f)(he:∀ s∈clip,Integrable (f s) μ): Hex k (fun s=> ∫ i,f s i ∂μ):=by
   have hF i: Integrable (pick k f i) μ:= integrable_finsetSum' _ (fun j _=> (he _ (probes k j)).smul (slate k j i)) -- edit
   refine ⟨fun i=> ∫ j,pick k f i j ∂μ,fun s hs=> ?_⟩; dsimp only; rw [h.seen hs]; simp_rw [Finset.sum_apply,Pi.smul_apply]; rw [integral_finsetSum]; simp_rw [integral_smul]; intro i _; exact (hF i).smul (mark k i s)
end YM.LocalLTE.Weft
