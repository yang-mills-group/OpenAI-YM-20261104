import YM.MSbar.Mosaic.Freedom
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
noncomputable def thorn (a:ℝ)(p:ℕ):ℝ:= αm a / (p+10:ℕ)
include hX
lemma thorn_top (p:ℕ): Tendsto (fun i:ι=> thorn (X i) p) φ (𝓝 0):=by
       have hv : Tendsto (fun i:ι=> ((hatW (X i))^3)⁻¹) φ (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n:=3) (by norm_num)).comp (Alto.broad.comp hX)) -- hX include
       unfold thorn αm; simp_rw [_root_.zpow_neg]; simpa only [zero_div] using! hv.div_const ((p+10:ℕ):ℝ)
-- ratio threshold.Tu align
include hG
lemma gate (h:Tendsto X φ atTop) (f:Side) (p:ℕ): ∀ᶠ x in φ,
        let u:= tip G f (X x); 0<thorn u p∧ (ray p (thorn u p)) ≤ αm u ∧ αm u ≤ Alto.cWidth u∧ αm u ≤ Alto.cWidth (X x)/(f.val:ℝ) :=by
    have hz:Tendsto (fun i=>hatW (tip G f (X i))) φ atTop:=Alto.broad.comp ((Work.E09.betaF_growth G f).comp hX); -- include hG for drift
    filter_upwards [hz.eventually_ge_atTop (f.val),hX.eventually (Alto.drift_scale hG f)] with i he hh u; let x:=hatW u; let y:=hatW (X i); have hf: 1 ≤ (f.val:ℝ):=Nat.one_le_cast.mpr f.property; have hx:1≤x:=hf.trans he; have hy:1≤ y:=hh.1;have hv:y≤ x:=hh.2.1
    have hx':=zero_lt_one.trans_le hx;have hy':=zero_lt_one.trans_le hy; let b:= x^(-3:ℤ); have hb:b=x⁻¹^ (3:ℕ):=by unfold b; rw [_root_.zpow_neg]; simp; rfl
    have hp:thorn u p=b/(p+10:ℕ):=rfl; have hb':0<b:=by rw [hb]; positivity
    rw [hp]; refine ⟨by positivity,?_ ,?_ ,?_⟩; · unfold ray; change _ ≤ b; rw [← mul_div_assoc]; apply (div_le_iff₀ (show 0 < ((p+10:ℕ):ℝ) from by positivity)).2; push_cast; nlinarith only [hb'] -- names
    · change b≤ 1/x^2; rw [hb, inv_pow, one_div]; exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hx (by omega))
    change b≤1/y^2/f.val; rw [hb, inv_pow,div_div,one_div]; apply inv_anti₀ ?_ ?_; exact mul_pos (pow_pos hy' _) (zero_lt_one.trans_le hf); apply le_trans (mul_le_mul_of_nonneg_left he (sq_nonneg y)); exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy'.le hv _) hx'.le) (le_of_eq (pow_succ x 2).symm)
variable (h₁:p+2 ≤ m)(ha:Run φ X f' 0)(hk:k=m+1) (hT:p+3≤ k)
include hX hχ hG hp hq hc h₁ ha hk hT
local notation "N"=> k*(p+2)
lemma hammer : ∃ T:ℝ,∃ ψ:ι→ℝ,Run φ (Y) ψ 0∧∀ᶠ x in φ, let R:= A x; let a:= αm (Y x)
       ∀ i≤p, Tokew (address R.F G) a 0 (N+k) 0 (PowerSeries.coeff i (singularity (pushChart R.F G R.v) 2)) T ∧
          Tokew (address R.F G) a 0 N 0 (PowerSeries.coeff i (barbed R.F R.v χ R.T)) (ψ x) ∧ (PowerSeries.coeff i (barbed R.F R.v χ R.T)).totalDegree ≤ N :=by
     obtain ⟨w,hw,hW⟩:= server hX χ J H H' K hG hp M i' hc h₁ ha
     have hy : Tendsto Y φ atTop:= (Work.E09.betaF_growth G K.L).comp hX
     obtain ⟨I⟩:=pre_order G H'.width H'.paths K.J D (by omega:3≤ k)
     let h: ℝ := Ruby.milkR I K 1 M.s (N+k) p; let g:ℝ :=Ruby.milkB I K χ 1 M.s N p
     let z(i):= g+ (M.st3^(N+1)*w i)
     refine ⟨h,z,(Run.wander hX G hG K.L _ _).1 ((Run.token hX g).addR hX (hw.mulK hX _)),?_⟩
     filter_upwards [hp,hc,hq,hW,gate hX hG hX K.L N, (Alto.broad.comp hy).eventually_ge_atTop 1] with i hp ⟨hf,Hx,hC,hM⟩ hq hh hk' hW; intro R a b he
     let A':= Alto.cWidth (Y i); have hx:R.passage (X i)=Y i:=by unfold passage; rw [hp.space] -- R
     have hx':0≤ a:=le_trans (show 0 ≤ ray N (thorn (Y i) N) from mul_nonneg (Nat.cast_nonneg _) hk'.1.le) hk'.2.1; have hz':0 < hatW (Y i):=zero_lt_one.trans_le hW; have he':a≤1:= hk'.2.2.1.trans ((one_div_le_one_div_of_le one_pos (one_le_pow₀ hW : 1≤ (hatW (Y i))^2)).trans_eq (div_one _))
     have h₀(k'):=(Ruby.antigen R.F R.v χ M.s I hq hp.payments.bends hχ 1 hx' he' p (by omega) k' _ he)
     have hG':= h₀ N; have hQ:=h₀ (N+k); have hu0 : R.S.patch=K:= hp.space; rw [hu0] at hG' hQ
     have hA: Tokew (Measuring.chart R.f G) a M.s N 0 (PowerSeries.coeff b R.T) (w i):=by
         have hu:= (hh b he|>.1.1); have hF(h:ℕ)(hl:h≤ m):=CrossH.token _ |>.mp hu |>.2 h hl
         apply Tokew.soft _ hk'.2.2.1 hx'
         have ht : (PowerSeries.coeff b R.T).totalDegree ≤ m+1:= (hf.preT.choose_spec.plane.profile _ he).trans (by omega)
         rw [hx] at hu; apply CrossH.token _|>.mpr; refine ⟨hu.1,fun j hp x=>?_⟩; by_cases he:j ≤ m; exact CrossH.token _|>.mp hu|>.2 j he x; rw [CrossH.whole _ ht _ (by omega)]; exact hu.1
     have hs:=hM.seats
     have hp0:Syrup (Measuring.chart R.f G) (address R.F G) a M.s (taps R.F G) M.st3:=by
          have hh:= hs.stamp -- use downgrade
          apply syrupDown _ _ hh _ le_rfl; rw [hp.space]; exact hk'.2.2.2
     have hp' := Ruby.blunt R.F R.v χ R.T M.s hG'.2 hA hp0 hx'; refine ⟨sunk (n:=0) (K:=0) (T:=0) hQ.1 le_rfl hx' (by omega), sunk (n:=0) (K:=0) (T:=0) hp' le_rfl hx' (by omega),?_ ⟩; refine (Parma.expanseB R.F R.v χ p R.T hf.preT.choose_spec.plane).1 b he |>.trans ?_; apply le_trans (b:=p+2); omega; nth_rw 1 [← one_mul (p+2)]; exact Nat.mul_le_mul_right _ (by omega)
end Issue
end YM.MSbar.Mosaic
