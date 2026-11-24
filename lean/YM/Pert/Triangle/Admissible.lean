import YM.Pert.Triangle.ShellWindow
/-! Borel control of the continuum test kernel; subtracted at the input with a translating ball, hence the separate integrations inside/outside the ball must also be read with this choice. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2200000
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Function Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3
local notation "P" => Points 3
variable (i t m n:I3)

def fullTransfer (G : Gauge) (p : P) := detector (p 1) (p 2) (p 0) G
def scorer (L:ℝ) (p:P) := ‖p 0‖^12 * stamp * classified (p 1) (p 2) (p 0)
def displacement (p:P) (i) := p i
lemma displacementDiff (i) : ContDiff ℝ ∞ (fun p:P=>p i) := (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _:Fin 3=>E4) i).contDiff -- params?
lemma positionMeas (i:Fin 3) : Measurable (fun p:P=>p i) := (displacementDiff i).continuous.measurable
lemma mLineMeas (a:Axis) : Measurable (mLine i a) := Finset.measurable_sum _ (fun b _=> (rayMeasurable (flow_rays b)).const_mul (fan false i b a))
lemma mixedMeas : Measurable (mixed i t) := rayMeasurable (mixed_rays i t)

local notation "O" => P × E4
def headFactor (s : O) := integralInput t m n (s.1 1) (s.1 2) s.2
def transferBall (s : O):Prop := s.2 ∈ zone (s.1 0) (s.1 1) (s.1 2)
def withinM (s : O):ℝ := innerZone i t m n (s.1 0) (s.1 1) (s.1 2) s.2
def outM (s : O):ℝ := outerZone i t m n (s.1 0) (s.1 1) (s.1 2) s.2
lemma headFactorColorMeas : Measurable (headFactor t m n) := by
  unfold headFactor integralInput
  refine Finset.measurable_sum _ (fun a _=> Finset.measurable_sum _ (fun b _=> ?_))
  have he (k i j : I3) := Measurable.comp (mLineMeas m a) (f:=fun s:O=>s.2-s.1 k) (measurable_snd.sub ((positionMeas _).comp measurable_fst))
  exact (by apply Measurable.mul; exact (he 1 0 0).const_mul _; exact Measurable.comp (mLineMeas n b) (f:=fun s:O=>s.2-s.1 2) (measurable_snd.sub ((positionMeas _).comp measurable_fst)))
lemma sectorMeas : MeasurableSet {s | transferBall s} := by
  have ep (j : Fin 3) : Measurable (fun p : O=>p.1 j) := (positionMeas j).comp (f:=(Prod.fst : O→P)) measurable_fst
  unfold transferBall; simp only [zone,mem_closedBall_iff_norm, pairHole]
  refine measurableSet_le (measurable_snd.sub (ep 0)).norm ?_
  exact (((ep 0|>.sub (ep 1)).norm.min ((ep 0 |>.sub (ep 2)).norm)).div_const _)
lemma withinMeas : Measurable (withinM i t m n) := by
  let f := headFactor t m n
  let F(z:O) := (z.1,z.1 0)
  have he : Measurable F := measurable_fst.prodMk ((positionMeas 0).comp measurable_fst)
  have hm (z:O): integralInput t m n (z.1 1) (z.1 2) (z.1 0) = f (F z) := rfl
  unfold withinM innerZone; simp_rw [hm]
  exact Measurable.ite sectorMeas ((mixedMeas i t |>.comp (f:=fun s:O=>s.1 0-s.2) ((positionMeas 0 |>.comp measurable_fst)|>.sub measurable_snd)).mul ((headFactorColorMeas ..).sub ((headFactorColorMeas ..).comp he))) measurable_const
lemma outMeas : Measurable (outM i t m n) := by
  unfold outM outerZone
  exact Measurable.ite sectorMeas.compl ((mixedMeas i t |>.comp (f:=fun s:O=>s.1 0-s.2) ((positionMeas 0 |>.comp measurable_fst)|>.sub measurable_snd)).mul (headFactorColorMeas ..)) measurable_const
lemma againstMeas : Measurable (fun p:P=>against i t m n (p 0) (p 1) (p 2)) := Measurable.add (f:=fun p=>∫ w, withinM i t m n (p,w)) (g:=fun p=>∫ w, outM i t m n (p,w))
  ((withinMeas i t m n |>.stronglyMeasurable).integral_prod_right' |>.measurable) ((outMeas i t m n).stronglyMeasurable.integral_prod_right'.measurable)
lemma impactMeas : Measurable (fun p:P=>impact (p 1) (p 2) (p 0) i m n) := by
  let f p t := against i t m n ((p:P) 0) (p 1) (p 2)
  change Measurable fun p:P=> _ - 2*∑t:I3,f p t
  let bm (k l a) := Measurable.comp (mLineMeas k a) (f:=fun p:P=>p 0-p l) ((positionMeas 0).sub (positionMeas l))
  have h : Measurable (fun p:P=>terminal (p 1) (p 2) (p 0) i m n) := Finset.measurable_sum _ (fun k _=> Finset.measurable_sum _ (fun l _=> ((bm m 1 k).mul (bm n 2 l)).const_mul _))
  exact h.sub ((Finset.measurable_sum _ (fun t _=> show Measurable (fun p=>f p t) from againstMeas _ _ _ _)).const_mul _)
lemma fullMeasurable (G : Gauge) : Measurable (fullTransfer G) := by
  let f(i j k m n:I3) (p:P) := ((eps3 i j k:ℤ):ℝ)*mixed j m (p 0-p 1) * mixed k n (p 0-p 2) * impact (p 1) (p 2) (p 0) i m n
  have he i j k m n : Measurable (f i j k m n) :=
    ((((mixedMeas j m).comp (f:=fun p:P=>p 0-p 1) ((positionMeas 0).sub (positionMeas 1))).const_mul _ |>.mul (((mixedMeas k n).comp (f:=fun p:P=>p 0-p 2) ((positionMeas 0).sub (positionMeas 2))))).mul (impactMeas i m n))
  exact (Finset.measurable_sum _ (fun i _=> Finset.measurable_sum _ fun j _=> Finset.measurable_sum _ (fun k _=>Finset.measurable_sum _ fun m _=>Finset.measurable_sum _ fun n _=> he i j k m n))).const_mul (6*_)

def suitable (K:ℝ) (p : P) : Prop := 10≤‖p 1‖ ∧ ‖p 1‖≤18 ∧ ‖p 2‖≤2 ∧ K≤‖p 0‖
lemma clock_clear (K:ℝ) (p:P) (h:suitable K p) (hK : 100≤K) : mask (p 1,p 2,‖p 0‖⁻¹ • p 0) := by
  refine ⟨mem_closedBall_iff_norm.mpr ?_, mem_closedBall_iff_norm.mpr ?_, mem_sphere_iff_norm.mpr ?_, ?_⟩
  · change ‖p 1 - 0‖ ≤ _; rw [sub_zero]; exact h.2.1
  · change ‖p 2 - 0‖ ≤ _; rw [sub_zero]; exact h.2.2.1
  · change ‖_ • _ - 0‖ = 1
    have he : ‖p 0‖ ≠ 0 := (show 0<‖p 0‖ from lt_of_lt_of_le (by linarith) h.2.2.2).ne'
    rw [sub_zero,norm_smul,Real.norm_of_nonneg (by positivity)]
    exact inv_mul_cancel₀ he
  have he := norm_sub_norm_le (p 1) (p 2)
  dsimp; linarith [h.1,h.2.2.1]
lemma suitable_separations (p:P) (h : suitable 100 p) :
    4 < ‖p 0 - p (1 : Fin 3)‖ ∧ 4 < ‖p 0 - p 2‖ ∧ 4 < ‖p 1 - p 2‖ := by
  refine ⟨by linarith [norm_sub_norm_le (p 0) (p 1),h.2.2.2,h.2.1],
          by linarith [norm_sub_norm_le (p 0) (p 2),h.2.2.2, h.2.2.1], by linarith [norm_sub_norm_le (p 1) (p 2), h.1,h.2.2.1]⟩
lemma clock_score (K:ℝ) (p:P) (h:suitable (max 100 K) p) : scorer K p = sphereRead (p 1,p 2,‖p 0‖⁻¹ • p 0) ‖p 0‖ := by
  unfold scorer sphereRead radial; rw [smul_smul,mul_inv_cancel₀,one_smul,mul_right_comm]
  exact (show 0<‖p 0‖ from lt_of_lt_of_le (by change 0 < max (100:ℝ) K; exact lt_max_of_lt_left (by norm_num)) h.2.2.2 ).ne'
end YM.Pert.Triangle
