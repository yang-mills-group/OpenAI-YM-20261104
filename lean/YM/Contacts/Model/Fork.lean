import YM.Contacts.Model.Pulse
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals Stationary Milling PertExtension.Series Exterior Precision Ion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c C:Side}{k w r z:ℕ}

open Push.Uniform Work.F02 Metric
variable {d:ℕ}{K: Type}[NormedAddCommGroup K][NormedSpace ℝ K] {x:K} {Z μ C' Y b:ℝ}{U:K→ Config G n}
-- Any chart size fixed E.G.Read Period. Exponential lease.
def allow (K μ: ℝ)(n : ℕ) := composeCost n ((1+(2:ℝ)^n / (Work.F02.radius (μ/2)))^n) K
lemma allow_pos (hw:0≤Z)(h:0<μ)(n:ℕ):0≤allow Z μ n:= by have hp:= Work.F02.radius_pos (half_pos h); unfold allow composeCost; positivity
-- per link Tint as chosen empirically
lemma arm_veil (i:Body 1 n): ‖(ContinuousLinearMap.proj i).comp (arm G n 1).toContinuousLinearMap‖ ≤ Push.Uniform.shade G:= by
  apply ContinuousLinearMap.opNorm_le_bound _ (Push.Uniform.shade_pos _).le; intro v
  let u(k:G.ColorIndex):= v (i.1,i.2,k); let x(p:Unit × G.ColorIndex):= u p.2
  apply le_trans (b:= ‖tint G Unit x ()‖); · exact le_of_eq rfl
  apply le_trans (norm_le_pi_norm (tint G Unit x) ()); apply le_trans (tint_le _); apply mul_le_mul_of_nonneg_left _ (Push.Uniform.shade_pos _).le
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 (fun i=>norm_le_pi_norm v _)
lemma imprints (h:PaintSupply G k Z) {x:Link G n}(hx:‖x‖≤1)(i:Bond n): Allows k (fun y=> G.mat (input G n y i)) x (outerCost G k Z) := by
  obtain ⟨a,b⟩:= i; let L:=(ContinuousLinearMap.proj (a,coord b)).comp (arm G n 1).toContinuousLinearMap; have he:‖L‖ ≤ Push.Uniform.shade G:= arm_veil _
  have hv:‖L x‖ ≤ Push.Uniform.shade G:= by apply (L.le_opNorm x).trans; exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans he
  simp_rw [encode_link]; exact (h.2 _ hv).comp (f:=⇑L) (allows_linear he hv)

lemma checkout (hs : 0<μ) (h:∀ i, Allows k (fun y=> G.mat (U y i)) x Z) (a:Site n)(q:RG.Slot) : Allows k (fun x=>q.atSite (U x) a) x (‖Work.F02.colorReal G‖* (|Work.F02.slotConst G| *allow Z μ k * Real.exp ((μ/2)*q.length))) := by
  let m:=μ/2; let P (z : K) := physical (U z); have hh := allows_real_of_entire k (Work.F02.slotExt_contDiff q (G:=G) a) (x:=P x)
    (Work.F02.radius_pos (half_pos hs)) (fun y hy =>
      (slotExt_bound (U x) (half_pos hs) y (ball_subset_closedBall hy) q a).trans
        (show _ ≤ |Work.F02.slotConst G| * Real.exp (m*q.length) from mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
  let M := |Work.F02.slotConst G| * allow Z μ k * Real.exp (m*q.length);
  have hy: Allows k (fun z=> slotExt q a (P z)) x M := by refine (hh.comp (f:=P) (allows_ambient (U:=U) h)).mono ?_; unfold M m allow composeCost; exact le_of_eq (by ring)
  apply (hy.linear (colorReal G) le_rfl).germ; exact Eventually.of_forall fun v=>by dsimp only [P]; rw [slotExt_physical,colorReal_up]
lemma rescue (hs : 0<μ)(h : ∀ i,Allows k (fun y=> G.mat (U y i)) x Z)(a:Site n)(q:RG.Atom G d) : Allows k (fun x=> q.unmasked (U x) a) x (allow Z μ k * ((q.budget (μ/2))* |slotConst G|^d)):= by
  let P z:=physical (U z); let m:= μ/2
  have hy : 0 ≤ q.magnitude := by unfold Atom.magnitude; positivity
  have hh := allows_real_of_entire k (Work.F02.atomExt_contDiff q a) (x:=P x) (Work.F02.radius_pos (half_pos hs))
    (fun y hv => (atomExt_bound q _ (half_pos hs) y (ball_subset_closedBall hv) a).trans (show _ ≤ q.budget m * |slotConst G|^d by
      by_cases h : 0 ≤ slotConst G; · rw [abs_of_nonneg h]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hy (Real.exp_pos _).le)
      rw [← abs_pow]; exact le_abs_self _))
  let M:= allow Z μ k * (q.budget m * |slotConst G|^d); have hj : Allows k (fun z=> atomExt q a (P z)) x M := by refine (hh.comp (f:=P) (allows_ambient (U:=U) h)).mono ?_; unfold M m allow composeCost; exact le_of_eq (by ring)
  have hy(v): Complex.reCLM (atomExt q a (P v))=q.unmasked (U v) a := by unfold P; rw [Work.F02.atomExt_physical]; rfl
  have ht:=hj.linear Complex.reCLM Complex.reCLM_norm.le; simp_rw [one_mul, hy] at ht; exact ht

-- weighted sum budgets to Allows. need eventual analytic from factor complex Lift separately.
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{ι:Type}
lemma attendance (P:ι→ K→E)(v:ι→ℝ) {s:Set K} (h:IsOpen s)(hp:IsPreconnected s)(hw:x∈s)(he:SumBudget v b)(hP:∀ i y,y∈s→Allows k (P i) y (v i))(ha: ContDiffAt ℝ ω (fun x=> ∑' i,P i x) x): Allows k (fun x=>∑' i,P i x) x b := by
   letI:CompleteSpace E:= FiniteDimensional.complete ℝ E; refine ⟨ha,fun j hj=>?_⟩
   rw [iterated_at_sum h hp he.2.1 hP hw j hj]; let f i:=iteratedFDeriv ℝ j (P i) x; have hx i: ‖f i‖ ≤ v i:= (hP i x hw).norm_le j hj
   have hh:= he.2.1.of_nonneg_of_le (fun i=> norm_nonneg (f i)) hx; exact (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum hx he.2.1).trans he.2.2)

-- exponential error on truncation
lemma marker (X:ι→ℝ)(Y:ι→ℕ)(h:∀ i,0≤ X i) (A: Set ι) (a:ℕ)(ha: ∀ i∈A,a≤ Y i)(hp: SumBudget (fun i=> X i* Real.exp (μ*Y i)) b)(hM:0≤μ): SumBudget (fun i:↥A=> X i*Real.exp ((μ/2)*Y i)) (Real.exp (-μ/2*a)*b):= by
   refine budget_mono (budget_scale (Real.exp_pos _).le (Pulse.budget_crop hp (p:=fun i=> i∈A))) (fun i=> mul_nonneg (h _) (Real.exp_pos _).le) ?_
   intro i; rw [mul_left_comm,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (h _); linarith only [mul_le_mul_of_nonneg_left (show (a:ℝ) ≤ Y i.val from Nat.cast_le.mpr (ha _ i.property)) hM]
end YM.Contacts.Model
