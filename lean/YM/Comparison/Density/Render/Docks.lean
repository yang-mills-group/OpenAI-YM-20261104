import YM.Comparison.Density.Reset.RowFactor
import YM.Push.FREE_RESOLVENT.Powers

/-!
Ordinary Lie jet prices for true group paths (real link-log representation,
not analytically continuing clipped masks). Through polynomials of arbitrary
fixed order. Uses nonabelian assembled-jets theorem with real winding lengths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render
open Fusing Markers Testing Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums Assembly Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo UVNext.CouplingReset Next.Scheduling Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {k : ℕ}
variable {X Y Z D : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma abroad {f : X→Y} {a c} (h : Through k f a c) (L : Y→L[ℝ]Z) : Through k (fun x=>L (f x)) a (‖L‖*c) := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth,fun i hi=>?_⟩
  exact (L.norm_iteratedFDeriv_comp_left h.smooth (by exact_mod_cast hi)).trans (mul_le_mul_of_nonneg_left (h.pay i hi) (norm_nonneg _))
lemma single_le {l : List (Fin k)} {m : ℕ} {f : X→Y} {A : X} {c : ℝ} (h : Through m f A c) (hl : l.length ≤ m)
    (v : Fin k → X) (he : ∀ i,‖v i‖ ≤ 1) : ‖FreeResolvent.TestD.jet v f l A‖ ≤ c:= by
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul (h.pay l.length hl) (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun _ _=> he _)) (prod_nonneg fun _ _=> norm_nonneg _) h.nonneg |>.trans ?_); simp
lemma stitch (t : Y→L[ℝ] Z→L[ℝ] D) {x : X} {a b : ℝ} {f : X→Y} {g : X→Z} (hf : Through k f x a) (hg : Through k g x b) :
    Through k (fun u=> t (f u) (g u)) x (2^k*(‖t‖*a*b)):= by
  refine ⟨smooth_product _ hf.smooth hg.smooth,fun j hj => list_op (by have := hf.nonneg; have := hg.nonneg; positivity) (fun l v hl H=> ?_)⟩
  rw [leibniz v t l (smooth_of_le hf.smooth (hl.trans_le hj)) (smooth_of_le hg.smooth (hl.trans_le hj))]
  refine (norm_sum_le ..).trans ((sum_le_sum (f:=fun i:Masks l=> ‖t (jet v f (lo l i) x) (jet v g (hi l i) x)‖) (g:=fun _=> ‖t‖*a*b) fun i _=> ?_).trans ?_)
  · apply le_trans ((t _).le_opNorm _); refine mul_le_mul ((t.le_opNorm _).trans (mul_le_mul_of_nonneg_left (single_le hf ((len_low l i).trans (hl.trans_le hj)) v H) (norm_nonneg _))) (single_le hg ((len_high l i).trans (hl.trans_le hj)) v H) (norm_nonneg _) (mul_nonneg (norm_nonneg t) hf.nonneg)
  rw [sum_const, card_univ, FreeResolvent.TestD.card,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right
  · exact_mod_cast pow_le_pow_right₀ (a:=(2:ℕ)) one_le_two (hl.trans_le hj)
  exact mul_nonneg (mul_nonneg (norm_nonneg t) hf.nonneg) hg.nonneg

lemma minus {x : X} {a b : ℝ} {f g : X→Y} (hf : Through k f x a) (hg : Through k g x b): Through k (fun y=>f y-g y) x (a+b) := by
  refine ⟨hf.smooth.sub hg.smooth, fun j hj => ?_⟩
  change ‖iteratedFDeriv ℝ j (f-g) _‖ ≤ _
  rw [iteratedFDeriv_sub_apply (smooth_of_le hf.smooth hj) (smooth_of_le hg.smooth hj)]; exact (norm_sub_le ..).trans (add_le_add (hf.pay _ hj) (hg.pay _ hj))

-- Use global smoothly parameterized log placements in calculus; applies at EVERY point of a designated real hull. Near-identity field requirement only for *cost of a letter*.
private lemma wordOp {f : X→ Config G n} (x : X) {a σ : ℝ} (h : 0≤a) (hh : 0<σ) (w : Walk) (o)
    (h₁ : ∀ (l : Step) (i : Site n), ContDiff ℝ k fun x=> G.mat (l.read (f x) i))
    (h₂ : ∀ (l : Step) (i : Site n), Through k (fun x=> G.mat (l.read (f x) i)) x a) :
    Through k (fun x=> G.mat (travel (f x) o w)) x (patchMoney G k σ a k * Real.exp (σ*w.length)) := by
  refine ⟨(travel_cd h₁ w o).contDiffAt, fun j hj=>list_op (mul_nonneg (patch_nn _ _ hh h _) (Real.exp_pos _).le) (fun l v he hz=>?_ )⟩
  exact (assembled_jets h₁ h hh (fun i b _ hl=> single_le (h₂ i b) hl v hz) w o l (he.trans_le hj)).trans (mul_le_mul_of_nonneg_right (patch_le hh h (he.trans_le hj)) (Real.exp_pos _).le)

def ticket (G : Gauge) (a : ℝ) (k : ℕ):= ‖(1:G.Mat)‖*(1+2^k*a)^k*Real.exp 1
lemma route_op {f : X→ Config G n} (x : X) {a : ℝ} (h : 0≤a) (w : Walk) (o)
    (h₁ : ∀ (l : Step) (i : Site n), ContDiff ℝ k fun x=> G.mat (l.read (f x) i))
    (h₂ : ∀ (l : Step) (i : Site n), Through k (fun x=> G.mat (l.read (f x) i)) x a) :
    Through k (fun x=> G.mat (travel (f x) o w)) x (ticket G a k * (1+(w.length:ℝ))^k) := by
  let N:ℝ:=1+w.length; let σ:=N⁻¹; have hN:1≤N:=le_add_of_nonneg_right (Nat.cast_nonneg _); have hN₁:= zero_lt_one.trans_le hN; have hσ:0<σ:=inv_pos.mpr hN₁
  refine (wordOp x h hσ w o h₁ h₂).mono ?_
  have hσx : σ ≤ Real.exp σ-1:= by linarith only [Real.add_one_le_exp σ]
  have hK:0≤2^k*a:=mul_nonneg (by positivity) h
  have hf:0≤1+2^k*a/(Real.exp σ-1):= by have := hσ.trans_le hσx; positivity
  have hc : 1+2^k*a/(Real.exp σ-1) ≤ (1+2^k*a)*N := by
    apply (div_le_iff₀ hN₁).mp; rw [div_eq_inv_mul]; apply (mul_add ..).le.trans
    apply add_le_add
    · rw [mul_one]; exact inv_le_one_of_one_le₀ hN
    rw [← mul_div_assoc]; apply (div_le_iff₀ (hσ.trans_le hσx)).mpr; rw [mul_comm]; exact mul_le_mul_of_nonneg_left hσx hK
  refine (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hσ.le|>.trans_eq (inv_mul_cancel₀ hN₁.ne'))) (patch_nn G k hσ h _)
     ).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf hc k) (norm_nonneg _)) (Real.exp_pos _).le).trans_eq ?_)
  rw [mul_pow]; unfold ticket; unfold N; ring

private lemma fare (G : Gauge) (k : ℕ): ∃ c≥0,∀ U:G.Color, ‖U‖≤1 → Through k (fun x=> G.mat (G.lieExp x)) U c := by
  obtain ⟨c,hc,H⟩:=Push.Uniform.exists_allows (f:=fun x=>G.mat (G.lieExp x)) (isCompact_closedBall (0:G.Color) 1) (fun _ _=> G.exp_jet.contDiffAt) k
  exact ⟨c,hc,fun x hx=> Through.control (H x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))⟩

abbrev meter_inverse (G : Gauge) := (starL' ℝ : G.Mat≃L[ℝ]G.Mat).toContinuousLinearMap
def meter (G : Gauge) (k : ℕ):= (fare G k).choose
lemma meter_nn (G : Gauge) (k : ℕ) : 0 ≤ meter G k:= (fare G k).choose_spec.1

lemma letter_cd (s : Step) (o : Site n) : ContDiff ℝ k fun x : Directions G n=> G.mat (s.read (increment 1 x) o):= by
  have he : ContDiff ℝ ω fun x : Directions G n=> G.mat (increment 1 x (s.used o)):= ((G.exp_jet.comp (contDiff_apply ..))).mul contDiff_const
  unfold Step.read; split
  · exact (meter_inverse G|>.contDiff.comp he).of_le le_top
  exact he.of_le le_top
set_option maxHeartbeats 400000 in
lemma letter_trace (s : Step) (o : Site n) {x : Directions G n} (hx : ‖x‖≤1) : Through k (fun x : Directions G n=> G.mat (s.read (increment 1 x) o)) x (meter G k) := by
  let f:= fun x : Directions G n=> G.mat (increment 1 x (s.used o))
  have hz : f = fun x : Directions G n=> G.mat (G.lieExp ((ContinuousLinearMap.proj (R:=ℝ) (s.used o)) x)):= by unfold f; simp [increment]
  have hp : Through k f x (fare G k).choose:= by
    let L : Directions G n →L[ℝ] G.Color:=ContinuousLinearMap.proj (s.used o)
    have hQ : ‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m=> (norm_le_pi_norm m (s.used o)).trans_eq (one_mul _).symm
    have ht := (fare G k).choose_spec.2 (L x) ((norm_le_pi_norm x (s.used o)).trans hx)
    rw [hz]; exact through_pull L hQ ht
  unfold Step.read; split
  · rw [show (fun x : Directions G n=> G.mat ((increment 1 x (s.used o))⁻¹))=fun x=>meter_inverse G (f x) from funext fun x=>G.mat_inv _]; let L:G.Mat→L[ℝ]G.Mat:=meter_inverse G
    have ht := abroad hp L
    have hx:=ContinuousLinearMap.opNorm_le_bound L zero_le_one fun x=> by change ‖star x‖ ≤ _; rw [norm_star,one_mul]
    exact ht.mono (mul_le_of_le_one_left hp.nonneg hx)
  exact hp

lemma worded (o : Site n) (w : Walk) {x : Directions G n} (hx: ‖x‖≤1) : Through k (fun y : Directions G n=> G.mat (travel (increment 1 y) o w)) x
    (ticket G (meter G k) k*(1+(w.length:ℝ))^k):= route_op x (meter_nn G k) w o letter_cd fun b j=> letter_trace b j hx
end YM.Comparison.Density.Render
