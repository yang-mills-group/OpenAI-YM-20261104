import YM.RG01.Kernel.Noise
/-! # Exact conditional moments and LOCAL analytic perturbation domain

 Read numerator relative to the *conditional* denominator, not the Haar
 partition at mesh nor the normalizer on output of StepData.noise. Here tag
 tilt is a canonical linear source-test (caller may encode more tests in the
 same manner); supports can be coupling-dependent on the frozen physical
 fine/coarse masks but aren't re-tested at z. Kernels and the full-law seed
 density R.eval are retained throughout. The variation of the normalization
 is paid USING that very real conditional denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset Lattice RG Wilson
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}{N n m:ℕ} (H:History G) (h:H.Selected)(V:Config G (H.S.side m n))(hm:m<N)
local notation "S" => H.levels.clock.op m n
open Wheel
include h hm
-- ratio for new V with frozen `F t`

def conditional(N m n:ℕ)(V':Config G (H.S.side m n))(F: (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n)→ℂ) := moment (expense H N m n V') (prior ..) F

theorem trade (F: (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n)→ℂ)
    (eps:Edge (Site (H.S.side m n))→ℝ)(V':Config G (H.S.side m n))(he:∀ i,eps i=0→ V' i=V i) :
    generating (expense H N m n V) (channel (H.levels.clock.op m n) (H.β N n (m+1)) eps V) (prior ..) F (encoded eps V V')=
      ((H.rep N n m).eval V':ℝ)/((H.rep N n m).eval V:ℂ) * conditional H N m n V' F:=by
  let f:=H.rep N n m; let K:=upper H N n m; let A:=Config G (H.S.side (m+1) n); let Z:= S; let g (t:Z.Choices)(U:A):ℂ:=Z.likelihood U t*(K.eval U)*F t U
  unfold conditional generating moment; rw [mul_sum]; apply sum_congr rfl; intro i hi
  rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with t
  have hx := noiseReal Z K.beta eps V i V' he t
  let d:=f.eval V'/f.eval V
  change (↑(_*Z.noise K.beta (Z.prediction t i) V*K.eval t/f.eval V):ℂ)*(F i t*Complex.exp (script Z K.beta eps V i t (encoded eps V V')))= ↑(f.eval V')/(f.eval V)*((↑(Z.likelihood t i*Z.noise K.beta (Z.prediction t i) V'*K.eval t/f.eval V'):ℂ)*F i t)
  have hd:(f.eval V':ℂ)≠0:=by exact_mod_cast (Extra.Histories.Tour.bright H h N n m hm.le V'|>.ne')
  let N(t':Config G (H.S.side m n)):ℂ:=Z.noise K.beta (Z.prediction t i) t'
  let a:=Complex.exp (script Z K.beta eps V i t (encoded eps V V')); change a*N V=N V' at hx
  push_cast; change (↑(Z.likelihood t i) * N V * ↑(K.eval t) / (f.eval V:ℂ))*(F i t*a) = _ * ((↑(Z.likelihood t i)*N V'* ↑(K.eval t) / (f.eval V':ℂ))*F i t)
  rw [← hx]; field_simp

theorem quotaReal (F: (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n)→ℂ)
    (eps:Edge (Site (H.S.side m n))→ℝ)(V':Config G (H.S.side m n))(he:∀ i,eps i=0→ V' i=V i) :
    quota (expense H N m n V) (channel (H.levels.clock.op m n) (H.β N n (m+1)) eps V) (prior ..) F (encoded eps V V')=
        conditional H N m n V' F:=by
  rw [quota,Pi.div_apply,trade H h V hm F eps V' he, trade H h V hm 1 eps V' he,show conditional H N m n V' 1=1 from (actual N H h V' hm).unit,mul_one]
  have hd(U:Config G (H.S.side m n)):((H.rep N n m).eval U:ℂ)≠0:=by exact_mod_cast (Extra.Histories.Tour.bright H h N n m hm.le U|>.ne')
  field_simp [hd _]

-- export exact conditional tested normalization (all t averaged BEFORE dividing)
private def insertedLaw (N m n:ℕ)(F:(H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n)→ℂ)(V:Config G (H.S.side m n)):=
    let Mp:=H.levels.clock.op m n; let R:=upper H N n m; ∑ t:Mp.Choices,(∫ U, F t U* (((Mp.likelihood U t*Mp.noise R.beta (Mp.prediction U t) V*R.eval U):ℝ):ℂ) ∂(prior ..))
omit h hm in
lemma rel (F: (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n)→ℂ): conditional H N m n V F=insertedLaw H N m n F V / (H.rep N n m).eval V:= by
  unfold conditional insertedLaw moment; rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _; rw [← integral_div]; apply integral_congr_ae; filter_upwards with j
  unfold expense; push_cast; ring

/-- Disk independent of period for discussed simultaneous source tilt of const
M (or costs bounded by 1 in sup of the WHOLE law), and any angular displacement
Y over weights eps s.t. β*κ*tariff*Σ eps≤1. In use with
the **real** left derivative scaling there is likewise no complex gauge path
or change of flags. -/
def signed {c f:Lattice.Side}(s:StepData c f)(β:ℝ)(eps:Edge (Site c)→ℝ)(V:Config G c)(j:s.Choices → Config G f→ℂ)(i:s.Choices)(t:Config G f): (Angles G c × ℂ) →L[ℂ]ℂ:=
   (channel s β eps V i t).comp (ContinuousLinearMap.fst ℂ _ _) + (j i t) • (ContinuousLinearMap.snd ℂ _ _)

omit h hm -- booked h supplied
lemma tagPrice {c f:Lattice.Side}(s:StepData c f)(hS:s.patch.Branches s.kernel G)(β:ℝ)(eps:Edge (Site c)→ℝ)(V:Config G c)
    (j:s.Choices → Config G f→ℂ)(ht:Bounded (prior G f) j 1)
    (h:∀ i,0 ≤ eps i)(he:|β*s.kernel.penalty| * tariff G*(∑ i,eps i) ≤1):
    Wheel (prior G f) (signed s β eps V j) 2:=by
  let H:=booked s β eps V hS h
  refine ⟨by norm_num,fun i t=>ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun z=> ?_,fun i z=> ?_⟩
  · change ‖channel s β eps V i t z.1 + j i t*z.2‖≤ 2*_
    rw [two_mul]; refine (norm_add_le ..).trans (add_le_add ?_ ?_)
    · have hx := (channel s β eps V i t).le_opNorm z.1
      have hh:= H.uniform i t
      exact hx.trans ((mul_le_mul_of_nonneg_right (hh.trans he) (norm_nonneg _)).trans ((one_mul ‖z.1‖).symm ▸ norm_fst_le z))
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (ht.2 i t)).trans (norm_snd_le _)
  exact (H.measurable _ _).add ((ht.1 _).mul aestronglyMeasurable_const) -- implicit z
include h hm
theorem denominator (eps:Edge (Site (H.S.side m n))→ℝ)(K:(H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n)→ℂ)(hK:Bounded (prior ..) K 1)
    (he:∀ i,0 ≤ eps i)(hs: |H.β N n (m+1)*(H.levels.clock.kernel.penalty)| * tariff G*(∑ i,eps i) ≤1):
    let Z:=signed (H.levels.clock.op m n) (H.β N n (m+1)) eps V K
    let M:=generating (expense H N m n V) Z (prior ..)
    AnalyticOnNhd ℂ (M 1) Set.univ ∧
     (∀ z∈ closedBall 0 (1/8:ℝ), 1/2 ≤ ‖M 1 z‖ ∧ ‖(M 1 z)⁻¹‖≤ 2 ∧ AnalyticAt ℂ (fun z=> (M 1 z)⁻¹) z) ∧
     (∀ F b (_:Bounded (prior ..) F b)(_ : 0≤b), AnalyticOnNhd ℂ (M F) Set.univ ∧
        ∀ k:ℕ, ConnectedActivityE6.Blaze.Brush k b 2 (M F) 0 ∧ ConnectedActivityE6.Blaze.Brush k (invoice k b) (2+2*2) (M F/M 1) 0)∧
     (∀ V' : Config G (H.S.side m n), (∀ i, eps i=0→V' i=V i) → ∀ F,
       (M F /M 1) (encoded eps V V',0)=conditional H N m n V' F) :=by
  intro Z M
  let μ:= prior G (H.S.side (m+1) n); let w:=expense H N m n V
  have hv := actual N H h V hm
  have ht:= tagPrice S (H.levels.blocks m n|>.branches) _ eps V K hK he hs
  have hp(F b)(h : Bounded μ F b)(hb:0≤b): AnalyticOnNhd ℂ (M F) Set.univ ∧
        ∀ k:ℕ, ConnectedActivityE6.Blaze.Brush k b 2 (M F) 0 ∧ ConnectedActivityE6.Blaze.Brush k (invoice k b) (2+2*2) (M F/M 1) 0 := ⟨ht.entire hv h hb,fun k=> ⟨ht.rawBrush hv h hb k,ht.receipt hv h hb k⟩⟩
  have hA:= hp (1:_) 1 ⟨fun _=>aestronglyMeasurable_const,fun _ _=>le_of_eq norm_one⟩ zero_le_one|>.1
  refine ⟨hA,fun z hz=> ?_,hp,fun X hi F=>?_⟩
  · have hZ:‖z‖ ≤ 1/8:= by rwa [Metric.mem_closedBall,dist_zero_right] at hz
    have hx :1/2 ≤ ‖M 1 z‖:= Wheel.base_nonzero hv ht (fun i x=>by
       exact ((Z i x).le_opNorm z).trans ((mul_le_mul (ht.uniform ..) hZ (norm_nonneg _) (by norm_num)).trans_eq (by ring)))
    refine ⟨hx,?_,(hA z (Set.mem_univ _)).inv (norm_ne_zero_iff.mp (ne_of_gt (show 0< ‖M 1 z‖ by linarith only [hx])))⟩ -- complex
    rw [norm_inv]; have hp:0< ‖M 1 z‖:=by linarith only [hx]
    rw [inv_le_comm₀ hp (by norm_num)]; simpa using! hx
  have hh F: M F (encoded eps V X,0)=generating w (channel S (H.β N n (m+1)) eps V) μ F (encoded eps V X):=by
    unfold M Z signed generating; apply congr_arg (moment w μ); funext i x; change _*Complex.exp (_ + _*0)=_; rw [mul_zero,add_zero]; rfl
  rw [Pi.div_apply,hh,hh]
  exact quotaReal H h V hm F eps X hi
end YM.RG01.Kernel
