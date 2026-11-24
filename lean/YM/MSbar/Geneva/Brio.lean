import YM.MSbar.Geneva.Anchor
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab
open Next.SectorChange Bulk Posture
variable {G:Gauge}{ι:Type}{X:ι→ℝ}{φ:Filter ι}(hX:Tendsto X φ atTop)
variable (P:Patch)(K:KernelChoices)(J:Voice G)
variable {α:ℝ}{n:ι→Side}(H:Stage)
variable (Q:(i:ι)→Rep G (n i)) (U:(i:ι)→Nesting G (n i)) (Z:G.ColorIndex) (k:ℕ)
variable (hv:∀ᶠ i in φ,FaceValue H (X i) (Q i))
local notation "μ" i=> Alto.cWidth (X i)
local notation "W₀" i=> Positions (Primary (n i) G)
local notation "D" i=> (Measuring.chart (n i) G)
variable {A t:ι→ℝ}
include hX
lemma prepareE :Run φ X (fun i=>(Alto.cWidth (X i))⁻¹) 0∧Tendsto (fun i=>Alto.cWidth (X i)) φ (𝓝 0)∧ Tendsto (fun i=>Alto.cWidth (X i)*radiusB (X i)) φ (𝓝 0):=by
    let f(i):= Alto.flurry (X i); have ht:Tendsto f φ atTop:= Alto.broad.comp hX; let g(i):= Alto.cWidth (X i); have hh : Tendsto g φ (𝓝 0):=tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp ht)
    refine ⟨?_,hh,?_⟩; · unfold Alto.cWidth; simp_rw [one_div,inv_inv]; exact (Run.stanza hX).Ypow hX 2
    let K(i):= (f i)^2; have hL:Tendsto (fun i=> (2:ℝ)/f i) φ (𝓝 0):= tendsto_const_nhds.div_atTop ht
    apply squeeze_zero' _ _ hL; refine Eventually.of_forall (fun i=>by unfold Alto.cWidth; positivity)
    filter_upwards [ht.eventually_ge_atTop 1] with i hi; have hx:(radiusB (X i):ℝ) ≤2*f i:= by
        have he:(radiusB (X i):ℝ)< f i+1:= Nat.ceil_lt_add_one (by positivity); linarith only [he,hi]
    have hk:0<f i:=zero_lt_one.trans_le hi; have hz:0≤ g i:= div_nonneg zero_le_one (sq_nonneg _); exact (mul_le_mul_of_nonneg_left hx hz).trans_eq (by change 1/f i^2*(2*f i)=_;field_simp)
lemma stars {p q:ℕ} (b c:ℝ) (he:Run φ X t 0) (h:Tendsto t φ (𝓝 0))(hp:Run φ X (fun i=>(t i)⁻¹) 0): Run φ X (fun i=> countCost (t i)) 0 ∧Run φ X (fun i=>pulp c (t i) b p q) 0 := by
    have ht(a:ℝ) : Run φ X (fun i=>Real.exp (t i*a)) 0 := Run.exp hX (h.mul_const a); have hh:Run φ X (fun i=> countCost (t i)) 0:=by
         unfold countCost; simp_rw [div_eq_mul_inv,← _root_.inv_pow]; exact ((((ht 2).mulY hX _).Ymul hX (hp.Ypow hX _)).mulY hX _)
    refine ⟨hh,?_⟩; unfold pulp; apply Run.Ymul hX ?_ hh; apply Run.mulK hX; exact Run.exp hX ((h.const_mul 3).mul_const _)
variable (hK:∀ᶠ i in φ, k≤ (Q i).p.order)(hL:∀ᶠ i in φ,0<t i∧t i ≤ 4*cue (X i))(hJ:Clear G J)
include P K J H hv hK hL hJ
lemma roar : ∃ c:ℕ,∃ a:ι→ℝ, Run φ X a c∧∀ᶠ i in φ,∀ x:Positions (Primary (n i) G),‖x‖≤ hull (X i) → Roil (Aqua.vine (Q i) (t i)) k (Alto.cWidth (X i)) x (a i):=by
    obtain ⟨hk,hg,H'⟩:= prepareE hX; let ω':=fun i=> μ i; have hP:=Run.Yplus hX hg
    obtain ⟨D₀,hD⟩:= paint_supply G k; let T:= H.width; have htT:0<T:= H.width_pos; obtain ⟨V,hU,HX⟩:= RawP.fund G k (T/2) (half_pos htT) D₀ hD; obtain ⟨v,h0,hA⟩:= sq_supply G (V*H.paths) k
    let a(i):= bust k G H.clip (Q i).p (ω' i) (Q i).beta D₀ H.paths V v (lbt (X i)) (ability (X i)); have hKσ: ∀ᶠ i in φ, Bash (ball (0:Positions (Primary (n i) G)) (2*t i*hull (X i))) (Q i).p:= (sizeF hX (fun i=>(Q i).p) J hJ n (hv.mono (fun i h=>h.threshold)) hL).mono fun i h=> h.2.2
    have hE : Run φ X (fun i=>(Q i).beta) 1 := by refine ((Run.core hX 1).mulK hX 2).cash ((hv.and (hX.eventually_gt_atTop 0)).mono (fun i hi=>?_)); rw [abs_of_pos ((half_pos hi.2).trans_le hi.1.beta),Real.rpow_one]; exact hi.1.upper.trans (le_abs_self _)
    let g(i):= T- 6*ω' i*k; have hT:Tendsto g φ (𝓝 T):= by simpa using! (tendsto_const_nhds (x:=T)).sub ((hg.const_mul 6).mul_const (k:ℝ)); -- 
    have hh : Tendsto (fun i=> 3*ω' i*k*(4*(Q i).p.B+2:ℕ)) φ (𝓝 0):=by
         have hZ:= (H'.mul_const ((12:ℝ)*k)).add (hg.mul_const (6*(k:ℝ))); simp only [zero_mul,add_zero] at hZ; refine hZ.congr' ?_; filter_upwards [hv] with i hi; rw [hi.size]; push_cast; ring
    have ht: Run φ X t (-(1/2)):= (Run.waxing hX|>.1.mulK hX 4).cash (hL.mono (fun i hi=>by rw [abs_of_nonneg hi.1.le]; exact hi.2.trans (le_abs_self _)))
    refine ⟨k+1,a,?_,?_⟩; swap
    · have ht':= (ht.bouquet hX (by norm_num)); filter_upwards [hK,hL,hKσ,hv,hg.eventually (ge_mem_nhds htT), hh.eventually (ge_mem_nhds H.price_pos),ht'.eventually (ge_mem_nhds zero_lt_one),hT.eventually (le_mem_nhds (half_lt_self htT)),(Alto.broad.comp hX).eventually_gt_atTop 0, (sizeF hX (fun i=>(Q i).p) J hJ n (hv.mono (fun i h=>h.threshold)) hL)] with i he ht hs hw hp hσ hk hg hN hn; intro x hx; have hb:0 ≤ hull (X i):=(norm_nonneg _).trans hx; let v':=t i; have hf:‖t i•x‖<2*t i*hull (X i):=by rw [norm_smul,Real.norm_of_nonneg ht.1.le]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx ht.1.le); linarith only [hn.1]
      have he':0 < μ i:= div_pos zero_lt_one (pow_pos hN 2); have htB : Brass G H.clip H.width H.paths (μ i) k (g i) D₀ V v:=by refine ⟨he',hD,(by unfold g T ω' ;ring), ⟨zero_le_one.trans hU,?_⟩,hA⟩; intro n w s b x hx; refine (HX n w s b x hx).mono ?_; gcongr
      have hh := RawP.residence H.width htB hw.clip hw.lawful (convex_ball ..) (mem_ball_zero_iff.mpr hf) Metric.isOpen_ball hs he (hf.trans_le hn.2.1) (le_trans hσ (Eq.le hw.support.symm)); exact tempoP _ hh (by rw [abs_of_nonneg ht.1.le]; exact hk) -- shadow
    -- rates
    let Cv(x):= lbt (X x); obtain ⟨_,_,hF,hW⟩:= melody hX P K G; have hC:Run φ X Cv 0:=Run.mulK hX hF _
    have hkQ(i):= stars hX (q:=i) (p:=k) H.paths V hP hg hk; let B(x):= ω' x
    have hP' : Run φ X (fun i=> pulp V (B i) (Cv i) k 2) 0:=by unfold pulp; apply Run.Ymul hX (Run.Ymul hX (hC.mulK hX _) ?_) ((hkQ k).1); exact Run.exp hX ((hg.const_mul 3).mul_const _)
    have he(t:ℝ):Run φ X (fun x=>Real.exp (3*B x*t)) 0:=Run.exp hX ((hg.const_mul 3).mul_const _)
    have hc: Run φ X (fun i=> kernelCost G H.clip H.paths D₀ V (B i) v k) 0 := by
         unfold RawP.kernelCost; refine Run.Ymul hX (Run.addR hX (Run.mulK hX (he _) _) ?_) (Run.mulK hX ((hkQ k).1) _); unfold RawP.bucket; exact Run.mulK hX (Run.mulK hX ((Run.addR hX (Run.token hX _) (Run.mulK hX (he _) _)).Ypow hX _) _) _
    have ht: Tendsto (fun i=> 3* (μ i)*k*(2*(Q i).p.B:ℕ)) φ (𝓝 0):=by
           have hvZ:= H'.mul_const (6*(k:ℝ)); rw [zero_mul] at hvZ; apply hvZ.congr'; filter_upwards [hv] with i hi; rw [hi.size]; push_cast; ring -- shadow
    have hg': Run φ X (fun i=> cork G (Q i).p k (B i)) (1/2*k):=by unfold cork; exact Run.Ycost hX (Run.exp hX ht) (peggy hX P K H Q hv k)
    let m:= -(1/2:ℝ); unfold a RawP.bust; apply Run.addR hX _ _; · apply Run.addR hX; exact (((hE.absA hX).Yrat hX ((hc.addR hX (hkQ 3|>.2)).addR hX (hkQ 4|>.2))).loosen (by exact_mod_cast (Nat.le_add_left 1 k))); exact hP'.loosen (Nat.cast_nonneg ..)
    exact ((hg'.mulR hX (hW.Yrat hX (hkQ k).1)).loosen (by push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) k]))
end YM.MSbar.Geneva
