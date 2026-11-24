import YM.XSpace.Rainier
/-! # Smooth location on every stage and cover -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function MeasureTheory Filter Set Relief Sail Playpen Trace Litter Octave Lattice Further.FreeCovariance.KP Tide
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y:ι→Cover}{u v:E4} {k:ℕ}
lemma value (h:distance L a x u)(H:distance L a y v):distance L a (fun i=> x i-y i) (u-v):= Stall.fence L u v h H
lemma ar_add (x y:Cover)(p:ℝ): actual p (x+y)=actual p x+actual p y:=by rw [actual,Cross.rcast_add,smul_add]; rfl
lemma ar_sub (x y:Cover)(p:ℝ): actual p (x-y)=actual p x-actual p y:=by rw [actual,Cross.rcast_sub,smul_sub]; rfl
lemma since (h:distance L a x u)(H:distance L a y v):distance L a (fun i=> x i+y i) (u+v):= (h.add H).congr fun i=> (ar_add ..).symm
lemma shines {p: Breeze}{f:Toe}(s: Relief.Stage L a)(h:distance L a x u)(hx:u≠0)(hp: Beam k f p): Tendsto (fun i=> (a i)⁻¹^k*f (x i)) L (𝓝 (p u)):=hp.beams s.good s.zero h hx []
-- uniform on a cover puncture in EUC current coords
lemma teaches (P:Toe)(h:P∈ Terrain k)(b:ℝ)(hB:0<b): ∃ C:ℝ,0<C∧ ∀ (p:ℝ)(x:Cover),0<p→ b≤ ‖actual p x‖→ ‖P x‖ ≤ C*p^k:=by
  obtain ⟨C,hC,H⟩:=sonar h; refine ⟨C*(2/b)^k,by positivity,fun p x hp h=>?_⟩; refine (H x).trans ((mul_le_mul_of_nonneg_left ?_ hC.le).trans_eq (?_ : C*( (p*(2/b))^k)=_)); swap
  · rw [mul_pow]; ring
  rw [rated]; have ht:0<pad x:=Drama.included _; gcongr
  unfold pad Drama.area; have hh:= (Shade.size_actual hp x).2; field_simp; nlinarith
variable (c:Shade.Cut)
def cash (p:ℝ):Toe:= fun x=> c (actual p x)
lemma store (p:ℝ)(x: Cover)(h:0<p): (↑(cash c p x):ℂ)= Shade.pace c p x:= (if_pos h).symm
lemma hand (X:Axis)(p:ℝ)(h:0<p)(x:Cover): (↑(η X (cash c p) x):ℂ)=Shade.turn X c p x:=by rw [Shade.turning,← store c p (x-step X) h,← store c p x h]; exact Complex.ofReal_sub ..
lemma lower (p:ℝ)(x:Cover): 0≤cash c p x:=c.nonneg
lemma higher (p:ℝ)(x:Cover): cash c p x≤1:=c.le_one
lemma cash_fee (p:ℝ)(x:Cover): ‖cash c p x‖≤1:= by rw [Real.norm_of_nonneg (lower ..)]; exact higher .. 
lemma make (s:Stage L a)(X:Axis):∃ K:ℝ,0≤K∧∀ᶠ i in L,∀ x:Cover, ‖η X (cash c (a i)) x‖ ≤ K*a i:=by
  obtain ⟨_,_,C,r,_,_,hC,h,H⟩:= Shade.seam_fees X c; refine ⟨C,hC,?_⟩; filter_upwards [s.zero.eventually (ge_mem_nhds h),s.good] with i hi ht x; rw [← Complex.norm_real,hand _ X _ ht]; by_cases he:Shade.turn X c (a i) x≠0; exact (H _ ht hi _ he).2.2; rw [Classical.not_not.mp he,norm_zero]; positivity
lemma shuffled (h: distance L a x u): Tendsto (fun i=> cash c (a i) (x i)) L (𝓝 (c u)):= c.continuous.continuousAt.tendsto.comp h
lemma muddled (s: Stage L a)(h: distance L a x u)(A:Axis): Tendsto (fun i=> (a i)⁻¹*η A (cash c (a i)) (x i)) L (𝓝 (-Maxwell.grad A (fun v=> c v) u)):= by
  have he:= Shade.saw A c s.zero s.good h; rw [map_neg] at he; refine (Complex.continuous_re.continuousAt.tendsto.comp he).congr' ?_; filter_upwards [s.good] with i hi; unfold comp; dsimp only; rw [← hand _ A _ hi, ← Complex.ofReal_inv, ← Complex.ofReal_mul]; rfl
lemma status (p:ℝ)(x:Cover)(h:cash c p x≠0): ‖actual p x‖≤c.rOut:= le_of_not_gt fun ht=> h (c.zero_of_le_dist (by simpa using ht.le))
lemma exc (p:ℝ)(x:Cover)(h:cash c p x≠1): c.rIn ≤ ‖actual p x‖:= le_of_not_gt fun ht=> h (c.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using ht.le))
-- budgets at separated anchors (all projections)
abbrev range (u v:E4):= 5*c.rOut < ‖u-v‖
def perch (p:ℝ)(w:Cover):Prop:= ‖actual p w‖ ≤ 2*c.rOut
lemma starter (p:ℝ)(w:Cover): cash c p w ≠0 → perch c p w := by intro h; unfold perch; linarith [c.rOut_pos,status c _ _ h]
lemma sentinel (p:ℝ)(hp:0<p)(h:p≤c.rOut)(X:Axis)(w:Cover): cash c p (w-step X)≠0→ perch c p w:=by
  intro ht; have he:= status c _ _ ht; rw [Shade.offset_turn] at he; unfold perch; calc
    _ ≤ ‖actual p w-p • basis X‖ + ‖p • basis X‖:= norm_le_norm_sub_add ..
    _ ≤ _:=by rw [norm_smul,basis_norm,Real.norm_of_nonneg hp.le]; linarith
lemma resolved (w x y:Cover)(p:ℝ)(h:4*c.rOut≤‖actual p (x-y)‖)(hv:perch c p (w-x)): c.rOut≤‖actual p (w-y)‖:=by
  have he:actual p (w-y)-actual p (w-x)=actual p (x-y):=by simp_rw [ar_sub]; abel
  rw [← he] at h; unfold perch at hv; linarith [norm_sub_le (actual p (w-y)) (actual p (w-x)),c.rOut_pos]
lemma toll (hp:range c u v)(hx:distance L a x u)(hy:distance L a y v): ∀ᶠ i in L,4*c.rOut≤‖actual (a i) (x i-y i)‖:= (value hx hy).norm.eventually (le_mem_nhds (lt_trans (by linarith [c.rOut_pos]:4*c.rOut<5*c.rOut) hp))
lemma range_sym (h: range c u v): range c v u:= by unfold range; rw [norm_sub_rev]; exact h
lemma gap (h:range c u v): u ≠ v:= fun he=> (lt_irrefl _) (by have hp:= c.rOut_pos; unfold range at h; rw [he,sub_self,norm_zero] at h; linarith : (0:ℝ)<0)
lemma perch_cost {p:ℝ}{w:Cover}(hp:0<p)(h:p≤ c.rOut)(hh:perch c p w): p * pad w ≤ 3*c.rOut:=by unfold perch at hh; unfold pad Drama.area; linarith [(Shade.size_actual hp w).1]
end YM.XSpace.Season
