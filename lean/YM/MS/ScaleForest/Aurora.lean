import YM.MS.ScaleForest.PeriTree
import YM.MS.Drops.Reeds
/-!
# Fourier integrals for time derivative channels

Compute the physical specialization of the beam ODE, using analysis of the
filed `Drops.ν` (pushes frequency volume to `planeF`) and dimension four,
at valid IR prescription. Proof doesn't erase an epsilon-dependent factor
except where it's justified by the z specialization of a holomorphic member
(like D). Then `receipt` and other open momentum tools are available. The
Laurent pole's leg outside the self-energy uses a **product** of two lines;
verify its finite length, not simply replacing it by a low momentum cutoff
factored once. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Aurora
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open Next Next.Rank Next.Rank.Beamer Next.Rank.Radian Prayer
open MS.Drops
open scoped Topology ContDiff BigOperators
variable {G : Gauge} (L K:Degree G)
-- x real point. Phase convention uses Theater.out coordinates
local notation "ν"=> Drops.ν
local notation "U"=>xy (fax L) (fax K)
local notation "Λ"=>Next.Rank.Radian.wave


def sunny (x:E4)(s:ℝ):= -harmon (stage0 L K s) x
lemma annual (w:E4)(s:ℝ): stage0 L K s w= -(U (ν w)* shining (m:=0) (ν w) s):= by
    rw [stage_v,sq_LP]; unfold shining City.brush; push_cast; simp only [neg_mul]; ring
lemma terminal_launch (x:E4)(s:ℝ): sunny L K x s=∫ p:QP, Tone.bill (Theater.out x) p * (U p * shining (m:=0) p s) ∂planeF:= by
    rw [sunny, Radian.wind,← integral_neg]; rw [← ampFπ.integral_comp (Drops.ν.toHomeomorph.measurableEmbedding) (fun p=>Tone.bill (Theater.out x) p*( U p* shining (m:=0) p s))]; apply integral_congr_ae; filter_upwards with w; rw [ν_bill, annual]; ring
lemma shine_int (x:E4)(s:ℝ): Integrable (fun p:QP=> Tone.bill (Theater.out x) p*(U p*shining (m:=0) p s)) planeF:= by
    rw [← ampFπ.integrable_comp_emb (Drops.ν.toHomeomorph.measurableEmbedding)]
    convert (listener _ (stage_h L K s) x).neg using 1; funext i; simp_rw [annual,Pi.neg_apply,mul_neg,neg_neg,comp,ν_bill]

-- retaining finite log length, then let IR end rise
abbrev firstS (x:E4)(s:ℝ): ℂ:= gleam L K x - γX L K x s
lemma first_d (x:E4)(s:ℝ): HasDerivAt (firstS L K x) (sunny L K x s) s:= by
    obtain ht:= receipt L K s x; rw [← Drops.budget ] at ht; exact ht.const_sub _ -- const_sub gives -f'
lemma first_out (x:E4) (hp:x≠0): Tendsto (firstS L K x) atBot (𝓝 0):= by
    have h:= dusk (whisper_s L K x hp); have ht:= h.neg; simpa only [neg_zero,neg_sub] using ht
lemma first_top (x:E4): Tendsto (firstS L K x) atTop (𝓝 ((gleam L K x):ℂ)):= by obtain he:= eitherI (width (l:=atTop) L K x) (by unfold hgt Epoch; omega); simpa only [sub_zero] using he.const_sub (↑(gleam L K x):ℂ)

-- the extended budget on the joined/pole channel, from symbol moments.
lemma quad_stage (p:E4) :
    stage0 L K 0 p=(2:ℂ)*( ∑ a:Axis,U (ν p)*press [a,a] (major (Pay 0)) p):= by
    unfold Next.Rank.Radian.press; simp_rw [annual, ← Finset.mul_sum ];
    have he(a:Axis) : crank a (crank a (major (Pay 0))) p = -(ν p a:ℂ)^2 * leaseTax 0 p:= by
       rw [show crank a (crank a (major (Pay 0))) p= _ from (press_H [a,a] (major (Pay 0)) p)]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; unfold leaseTax; ring_nf; rw [Complex.I_sq]; ring
    change -(_* shining (m:=0) _ 0)=2*(U (ν p) *∑ a:Axis, crank a (crank a _) p); rw [ shining ]; simp_rw [List.foldr_nil,he,sq_LP, ← Finset.sum_mul, Finset.sum_neg_distrib ]; simp only [ City.brush,exp_zero, one_pow,mul_one,one_mul,← Complex.ofReal_pow,← Complex.ofReal_sum,Momentum.sq]; push_cast; ring_nf

private def flash (k: List Axis)(u:ℝ)(t:E4):= U (ν t)* press k (major u) t
private lemma pressed_chain (k l:List Axis)(F:E4→ℂ): press k (press l F)=press (k++l) F:= (by simp [Next.Rank.Radian.press])
-- use primary_v instead of explicit phase IBP
lemma allait {u:ℝ}(hu:0<u)(k:List Axis)(n:ℕ): ∃ C:ℝ,0≤ C ∧ ∀ z:E4,1≤‖z‖→ ‖harmon (flash L K k u) z‖≤ C/‖z‖^n:= by
   choose C hC hB using (fun i j:Axis=> primary_v (raypath L K++[i,j]++k) hu n); let c:ℝ:= ∑ i,∑ j,C i j;
   have he i j:C i j ≤ c:= (Finset.single_le_sum (fun j _=>hC i j) (Finset.mem_univ j)).trans (Finset.single_le_sum (fun i _=> Finset.sum_nonneg fun j _=> hC i j ) (Finset.mem_univ i)); obtain hc: 0≤c:= le_trans (hC 0 0) (he _ _);
   refine ⟨ 4*c,by positivity,fun z hz=>?_⟩; unfold flash; rw [funext ( front L K ( press k (major u) ) ), harmon_feather L K _ (fun i j=> Moment.pressed _ (Moment.pressed _ ( majorM hu ))) ]; unfold paints; split; swap; · change ‖(0:ℂ)‖ ≤ _; rw [norm_zero]; positivity
   rw [Pi.smul_apply,norm_smul]; simp only [norm_pow,norm_neg,norm_one,one_pow,one_mul]; rw [ mul_div_assoc ]; refine sparse_heat _ _ _ _ _ _ fun i j=>?_ ; rw [pressed_chain]; exact (hB i j z hz).trans (div_le_div_of_nonneg_right (he i j) (pow_nonneg (norm_nonneg _) n))
lemma assorted (z:E4) : sunny L K z 0= -(2:ℂ)*(∑ a:Axis,harmon (flash L K [a,a] (Pay 0)) z) := by
   rw [sunny, Radian.wind]; simp_rw [quad_stage,Radian.wind]; unfold flash;
   rw [show (fun y:E4=> Λ z y * (2*(∑ a:Axis,U (ν y) * press [a,a] (major (Pay 0)) y)))=(fun y:E4=> 2* (∑ a:Axis,Λ z y*(U (ν y)*press [a,a] (major (Pay 0)) y))) from (by ext1 y; rw [mul_left_comm]; rw [ Finset.mul_sum ]) ]; rw [integral_const_mul, integral_finsetSum];
   ring; intro a _; exact listener _ (downE L K ((majorM (pay_positive 0)).pressed [a,a])).integral z
lemma sunny_bound (n:ℕ): ∃ C:ℝ,0≤ C ∧∀ z:E4,1≤‖z‖→ ‖sunny L K z 0‖≤ C/‖z‖^n:= by
   choose C hC hV using fun i:Axis=>allait L K (pay_positive 0) [i,i] n; refine ⟨ 2*∑ i:Axis,C i, mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _=>hC i),fun z hz=>?_⟩; rw [assorted,norm_mul]; simp only [norm_neg,Complex.norm_ofNat,mul_div_assoc]; exact mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans ( (Finset.sum_le_sum fun i _=> hV i z hz).trans (le_of_eq ( Finset.sum_div .. |>.symm ) ))) (by norm_num)
lemma sunny_total : ∃ C:ℝ,0≤ C ∧∀ x:E4, ‖sunny L K x 0‖≤ C:= by
   refine ⟨ ∫ p, ‖stage0 L K 0 p‖, integral_nonneg fun _=> norm_nonneg _,fun x=>?_ ⟩; unfold sunny; rw [norm_neg,Radian.wind]; apply (norm_integral_le_integral_norm _).trans; simp only [norm_mul,price_wave,one_mul]; exact le_rfl

variable (h: L.degree=0) (h':K.degree=0)
include h h'
private theorem strengthV (t:ℝ) (p:QP):
    let s:= exp t; U (s • p)*shining (m:=0) (s • p) 0=U p*shining (m:=0) p t := by
    intro s; rw [slot_s]; simp only [Epoch, h,h', Nat.zero_add]; unfold shining; simp only [City.brush,scaling,exp_zero,one_pow,mul_one,one_mul]; unfold s; push_cast [Complex.real_smul]; ring
lemma reach (s:ℝ)(x:E4) : sunny L K x s=(exp s ^4)⁻¹ • sunny L K ((exp s)⁻¹ • x) 0:= by
    let r:=exp s; let v:=r⁻¹ • x; let f(p:E4):= Λ v p *stage0 L K 0 p;
    have ht := exp_pos s; unfold sunny; simp_rw [Radian.wind]; rw [smul_neg]; apply congr_arg (-·); change _= (r^4)⁻¹ • ∫ p,f p;
    obtain hu:= Measure.integral_comp_smul_of_nonneg MeasureTheory.volume f r (hR:=ht.le); rw [Radian.spaceD] at hu; rw [← hu]; refine integral_congr_ae (Eventually.of_forall fun p=>?_); dsimp only;
    rw [show Λ x p= Λ v (r • p) from Eq.trans (show _=Λ (r • v) p from (congr_arg (fun x:E4=> Λ x p) (smul_inv_smul₀ ht.ne' x)).symm ) ( Drops.aim v p r )]; unfold f; rw [annual,annual,map_smul,strengthV L K h h'];
lemma sunny_bot (x:E4)(hx:x≠0) : Tendsto (sunny L K x) atBot (𝓝 0):= by
    obtain ⟨C,hC,hV⟩:= sunny_bound L K 5; have ht : 0<‖x‖:= norm_pos_iff.mpr hx;
    apply squeeze_zero_norm' (a:=fun s=> C/‖x‖^5 *exp s) ?_ (by simpa only [mul_zero] using tendsto_exp_atBot.const_mul (C/‖x‖^5))
    filter_upwards [tendsto_exp_atBot.eventually (gt_mem_nhds ht)] with s hs; rw [reach L K h h' ]; let r:=exp s; have hr:0<r:= exp_pos s; have hk: ‖r⁻¹ • x‖ = ‖x‖/r:= by unfold r; rw [norm_smul_of_nonneg (by positivity)]; ring
    obtain H:= hV (r⁻¹ • x) (by rw [hk]; field_simp; exact (show exp s<‖x‖ from hs).le); rw [hk] at H;
    refine Eq.trans_le (norm_smul_of_nonneg (show 0≤ (r^4)⁻¹ from by positivity) _) ((mul_le_mul_of_nonneg_left H ( by positivity )).trans_eq ?_); unfold r; field_simp
lemma sunny_end (x:E4) : Tendsto (sunny L K x) atTop (𝓝 0):= by obtain ⟨C,hC,hL⟩:= sunny_total L K; refine squeeze_zero_norm (fun t:ℝ=> show ‖sunny L K x t‖ ≤ ( exp t^4 )⁻¹*C from ?_) ?_; rw [reach L K h h', norm_smul_of_nonneg (by positivity) ]; exact mul_le_mul_of_nonneg_left (hL _) (by positivity); simp_rw [← inv_pow]; simpa only [zero_pow (show 4≠0 from (by omega)),zero_mul,comp_apply] using ((tendsto_inv_atTop_zero.comp tendsto_exp_atTop).pow 4).mul_const C
end YM.MS.ScaleForest.Aurora
