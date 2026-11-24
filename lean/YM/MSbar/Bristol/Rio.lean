import YM.MSbar.Bristol.Tours
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {A w B C b r a d v Y e:ℝ}{p i j m k s:ℕ}
local notation "V"=>PowerSeries ℝ
local notation "μ"=> PowerSeries.coeff
variable {f:PowerSeries ℝ}
lemma mini (h:Belt p f ≤ B)(hh:i ≤ p) :Belt i f ≤ B:= le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hh _)) (fun _ _ _ => abs_nonneg _)) h
lemma remainderM (h:Belt p f ≤ B)(hh:i ≤ p)(hd:0≤ r)(he:r ≤ 1): |taste p f r-taste i f r| ≤ r^(i+1)* B:=by
      unfold taste; let s:=range (i+1); let t:=range (p+1); let g(i:ℕ):= r^i * μ i f; have hv:s⊆t:= Finset.range_mono (Nat.add_le_add_right hh _); rw [show ∑ j∈t,g j-∑ j∈s,g j= _ from eq_sub_of_add_eq (Finset.sum_sdiff hv: (∑ i∈ t\s,g i) + ∑ j∈s,g j=∑ j∈t,g j) |>.symm]; -- pattern unfolding failed.simpa
      refine (abs_sum_le_sum_abs ..).trans ?_; let H:=∑ i∈t\s,|μ i f|; have he': H≤B:= le_trans (Finset.sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _=> abs_nonneg _)) h
      apply le_trans _ (mul_le_mul_of_nonneg_left he' (pow_nonneg hd (i+1))); unfold H; rw [Finset.mul_sum]; apply sum_le_sum; intro j hk; obtain ⟨h1,h2⟩:=mem_sdiff.mp hk; have he':i+1 ≤ j:= le_of_not_gt (fun hp=>h2 (mem_range.mpr hp)); unfold g; rw [abs_mul,abs_pow,abs_of_nonneg hd]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hd he he') (abs_nonneg _)
lemma temperatureP (g K:ℝ)(hα:μ 0 f=1)(h: Belt p f≤B)(hv:Belt p f⁻¹≤ C)(hs:0≤r)(hh:r ≤1)(hP:0< g)(he:g⁻¹ ≤ K): |g⁻¹-taste p f⁻¹ r| ≤ K*C*( r^(p+1)* B+ |g-taste p f r|):=by
    let t(f:V):=taste p f r; have hc:0 ≤ C:=(Belt_pos ..).trans hv; have hB:0 ≤ B:=(Belt_pos ..).trans h; let b:= taste p f r; let c:= t f⁻¹
    have hM : |1-b*c|≤r^(p+1)*(B*C):=by
         have hp: f*f⁻¹=1:= PowerSeries.mul_inv_cancel _ (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,hα]; norm_num); have hx:= (taste_mul p r hs hh f f⁻¹); rw [hp,single] at hx
         exact hx.trans (mul_le_mul_of_nonneg_left (mul_le_mul h hv (Belt_pos ..) hB) (pow_nonneg hs _))
    have hξ : |1-g*c| ≤ r^(p+1)*(B*C)+|g-b| * C:=by
         rw [show _ - _=(1-b*c)-(g-b)*c by ring]; refine (abs_sub ..).trans (add_le_add hM ((abs_mul ..).le.trans (mul_le_mul_of_nonneg_left ((taste_pays hs hh _).trans hv) (abs_nonneg _))))
    have hX: g⁻¹-c=g⁻¹*(1-g*c):=by field_simp
    have hP:= inv_pos.mpr hP; rw [hX,abs_mul,abs_of_pos hP]; unfold c t b at hξ; exact (mul_le_mul he hξ (abs_nonneg _) (hP.le.trans he)).trans_eq (by ring)
lemma atomP (u v:ℝ)(i:ℕ){K:ℝ}(he:|u|≤K)(hp:|v|≤K)(hK:1 ≤ K):|u^i - v^i| ≤ (i:ℝ)*K^i*|u-v|:=by -- K unbound
    induction i with
    | zero=>simp
    | succ i ih=>
                 rw [pow_succ,pow_succ v, show _*_ - _*_=(u^i-v^i)*u+v^i*(u-v) by ring]
                 apply (abs_add_le ..).trans; rw [abs_mul,abs_mul,abs_pow, Nat.cast_add_one]; have hK0:0≤ K:=zero_le_one.trans hK; exact (add_le_add (mul_le_mul ih he (abs_nonneg _) ((abs_nonneg _).trans ih)) (mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (abs_nonneg _) hp _).trans (pow_le_pow_right₀ hK (Nat.le_succ i))) (abs_nonneg _))).trans_eq (by simp only [pow_succ]; ring)
variable (f:PowerSeries ℝ)
noncomputable def priceV (K B:ℝ)(i j:ℕ):= (i:ℝ)*K^(i+j+2)*B -- instead
noncomputable def tonK (K:ℝ)(i j:ℕ):= (i:ℝ)*K^(i+j)+ (j:ℝ)*K^(j+i)*( K*(K*K+K)) +K^(i+j)+(i:ℝ)*K^(i+j)+(j:ℝ)*K^(j+i)
-- bound δ=u-v plus t^(p+1), poly coeff K. powers
lemma scent (g:ℝ)(h:μ 0 f=1)(hg: 0<g)(hV: |g|≤A)(he:g⁻¹≤A)(ht:Belt p f ≤ A)(hp:Belt p f⁻¹ ≤ A)(hh:1 ≤ A)(hy:0≤r)(hk:r ≤1)(i j:ℕ):|g^i*g⁻¹^j-taste p (f^i*f⁻¹^j) r|≤ tonK A i j*( |g-taste p f r|+r^(p+1)):=by
     let k:=taste p f r; let b:=taste p f⁻¹ r; let Y:= |g-k|; let Vv:= r^(p+1); have hy':|g-k|≥0:=abs_nonneg _; have hyV:0≤ Vv:=pow_nonneg hy _; have hG: |g⁻¹|≤ A:= (abs_of_pos (inv_pos.mpr hg)).trans_le he; have hv:|k| ≤ A:= (taste_pays hy hk _).trans ht; have hp': |b|≤ A:= (taste_pays hy hk _).trans hp; have h0:=zero_le_one.trans hh
     have heK:=pow_nonneg h0 i
     have hD':0 ≤ (j:ℝ)*A^j:=by positivity
     have hB: |b-g⁻¹|≤ A*(A*A+A)*(Y+Vv):=by
          rw [abs_sub_comm]; apply le_trans (temperatureP g A h ht hp hy hk hg he) -- supply
          change A*A*(Vv*A+Y)≤ A*(A*A+A)*(Y+Vv); have hZ: 0 ≤ Y:=hy'; linarith only [mul_nonneg (mul_nonneg (sq_nonneg A) h0) hZ, mul_nonneg (sq_nonneg A) hyV]
     let v(i:ℕ):=taste p (f^i) r; let φ(j:ℕ):=taste p (f⁻¹^j) r
     have hv0(j:ℕ):Belt p (f^j) ≤ A^j:=(Belt_tone ..).trans (pow_le_pow_left₀ (Belt_pos ..) ht _);
     have ht0(j:ℕ):Belt p (f⁻¹^j)≤ A^j:=(Belt_tone ..).trans (pow_le_pow_left₀ (Belt_pos ..) hp _)
     have hx: |g^i*g⁻¹^j-k^i*b^j| ≤ ((i:ℝ)*A^(i+j)+(j:ℝ)*A^(j+i)*(A*(A*A+A)))*(Y+Vv):=by
          rw [show _-_=(g^i-k^i)*g⁻¹^j+k^i*(g⁻¹^j-b^j) by ring]; apply (abs_add_le ..).trans; rw [abs_mul,abs_mul]; have ht:|g^i-k^i|≤ ↑i*A^i*(Y+Vv):= (atomP _ _ _ hV hv hh).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hyV) (by positivity))
          rw [abs_sub_comm b] at hB; refine (add_le_add (mul_le_mul ht (abs_pow .. |>.trans_le (pow_le_pow_left₀ (abs_nonneg _) hG _)) (abs_nonneg _) ((abs_nonneg _).trans ht)) (mul_le_mul (abs_pow ..|>.trans_le (pow_le_pow_left₀ (abs_nonneg _) hv _)) ((atomP _ _ _ hG hp' hh).trans (mul_le_mul_of_nonneg_left hB hD')) (abs_nonneg _) heK)).trans_eq ?_
          ring -- fill atom args
     have hξ:|k^i*b^j-v i*φ j|≤ ((i:ℝ)*A^(i+j)+(j:ℝ)*A^(j+i))*Vv:=by
          have hφ: |v i-k^i|≤ ↑i*Vv*A^i:=(taste_power f p i hy hk).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Belt_pos ..) ht i) (by positivity)) -- supply
          have he:|φ j-b^j|≤ ↑j* Vv * A^j:=(taste_power (f⁻¹) p j hy hk).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Belt_pos ..) hp j) (by positivity)); rw [abs_sub_comm] at hφ he
          rw [show _-_=(k^i-v i)*b^j + v i*(b^j-φ j) from by ring]; apply (abs_add_le ..).trans; rw [abs_mul,abs_mul]; exact (add_le_add (mul_le_mul hφ ((abs_pow ..).trans_le (pow_le_pow_left₀ (abs_nonneg _) hp' j)) (abs_nonneg _) ((abs_nonneg _).trans hφ)) (mul_le_mul ((taste_pays hy hk _).trans (hv0 _)) he (abs_nonneg _) heK)).trans_eq (by ring)
     have hx':|v i *φ j- taste p (f^i*f⁻¹^j) r|≤ Vv*(A^i*A^j):= by rw [abs_sub_comm]; exact (taste_mul p r hy hk _ _).trans (mul_le_mul_of_nonneg_left (mul_le_mul (hv0 i) (ht0 j) (Belt_pos ..) heK) hyV)
     apply (abs_sub_le _ (k^i*b^j) _).trans; apply le_trans (add_le_add hx ((abs_sub_le _ (v i*φ j) _).trans (add_le_add hξ hx')))
     unfold tonK; change _ ≤ _ * (Y+Vv); refine (add_le_add_right (add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0≤Y from hy')) (by positivity)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (show 0≤Y from hy')) (by positivity))) _).trans_eq ?_; ring
end YM.MSbar.Bristol
