import YM.Contacts.Loom.Earned
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Capture
open PertExtension.Series Radial Milling
variable {U W: Mint E α}{x:Frame α E}{d:ℕ→ℝ} {n h:ℕ}{T P:ℕ→ Mint E α}
lemma Budget.limits (h:Budget N x k p U)(ht:p<0)(ε:ℝ)(hp:0<ε) : ∀ᶠ i in atTop,∀ j:α i,‖U i j (x i j)‖<ε:= by
   obtain ⟨f,hf,H⟩:= (Arms.pick_const h).cap; filter_upwards [H,sliding hf ht _ hp] with i hi hx j using (hi.2 j).trans_lt ((le_abs_self _).trans_lt hx)
lemma Budget.mend (h: Budget N x k p (U-1))(ht:p<0): Budget N x k 0 U:= by rw [show U= (U-1)+1 from (sub_add_cancel ..).symm]; exact (Arms.lo h ht.le le_rfl).sum (Loom.Budget.tally (fun _=>1) (Rush.settle _))
-- neighbourhood.Seams in all Ω.
lemma positive (ht:p<0)(h: Budget N x k p (U-1)) : ∀ᶠ i in atTop,∀ j:α i,∀ᶠ y in 𝓝 (x i j),0<U i j y:= by
   obtain ⟨f,hf,H⟩:= (Budget.mend h ht).cap; filter_upwards [Budget.limits h ht 1 zero_lt_one,H] with i hi hx j; have hh : 0<U i j (x i j):= by have h:= (abs_lt.mp (show ‖U i j (x i j)-1‖<1 from hi j)).1; linarith
   exact (hx.2 j).smooth.continuousAt.eventually (lt_mem_nhds hh)
lemma capper (v:ℝ→ℝ)(he:AnalyticAt ℝ v 0)(hq:q<0): Root (F:=fun _=>ℝ) N (fun _=> v) k 0 (N.pow q) := by
   obtain ⟨s,hz,hS⟩:= Brush.neighborhood (k:=k) 0 he.contDiffAt; obtain ⟨d,hd,H⟩:= Metric.mem_nhds_iff.mp hS; refine ⟨⟨fun _=> s,Rush.settle _,?_⟩, Eventually.of_forall (fun _=> he)⟩; filter_upwards [sliding (M:=N) (f:=N.pow q) Rush.any hq _ hd] with i hi; exact ⟨hz.le,fun j=>H (ball_subset_ball ((le_abs_self _).trans hi.le) (show j.val ∈ ball (0:ℝ) (N.pow q i) from j.2))⟩
lemma sees (h:Budget N x k p U) (v:ℝ→ℝ)(he:AnalyticAt ℝ v 0)(hp:p<q)(hq:q<0): Budget N x k 0 (fun i j=>v ∘ U i j):= Loom.Budget.graft (Arms.port (capper v he (N:=N) hq|>.price) ((Pouch.canon.bank (p:=q) h hp).mono fun i hi j=>mem_ball_zero_iff.mpr (hi j))) h (hp.trans hq).le
lemma wake (h:Budget N x k p U)(v:ℝ→ℝ)(he:AnalyticAt ℝ v 0)(ht:1≤k)(hv:v 0=0)(hp:p<q)(hq:q<0) : Budget N x k q (fun i j=>v ∘ U i j):= by
    let V:=capper (k:=k) v he (N:=N) hq; let hv₁:=Pouch.canon (N:=N) (p:=q); have hh:=Root.application (S:=fun _=>v) (V.snap (N:=N) hv₁ ht (Eventually.of_forall fun _ i hi=> by interval_cases i; ext; simp [hv]) hq) (hv₁.bank h hp) hv₁ h hp.le; simpa only [Nat.cast_one, zero_add,mul_one] using hh
lemma nozzle (w: Budget N x k p (U-1))(hp:p<0): Budget N x k 0 (U⁻¹):= by
   let f (u:ℝ):=(1+u)⁻¹; have hx: AnalyticAt ℝ f 0:= (analyticAt_const.add analyticAt_id).inv (by norm_num); refine Arms.cheaper ?_ (sees w f hx (by linarith : p < p/2) (by linarith)); ext x j k; change (1+(U x j k-1))⁻¹= _; rw [add_sub_cancel]; rfl -- direction
-- stable log difference for ratios. both received. no branch y calculation.
def grant (U:Mint E α): Mint E α:= fun i j=> Real.log ∘ U i j
lemma corresponding (h:Budget N x k p (U-1))(hu:p<0)(he:Budget N x k r (W-U)) (ht:1≤k)(hp:r<q)(hq:q<0): Budget N x k q (grant W-grant U):= by
    let b:= (W-U)*U⁻¹; let f (u:ℝ):= Real.log (1+u); have hb:= Loom.Budget.mul _ _ he (nozzle h hu) (add_zero r); have hf: Budget N x k q (fun i j=> f ∘ b i j):= wake hb f (analyticAt_const.add analyticAt_id|>.log (by norm_num)) ht (by simp [f]) hp hq
    have hh : Budget N x k (max p r) (W-1):= Arms.cheaper (sub_add_sub_cancel W U 1) ((Arms.lo he (le_max_right ..) le_rfl).sum (Arms.lo h (le_max_left ..) le_rfl)); refine Arms.reveal hf (( (positive hu h).and (positive (max_lt hu (hp.trans hq)) hh)).mono fun i hi j=>?_ ) le_rfl le_rfl
    filter_upwards [hi.1 j,hi.2 j] with y hy ht; change Real.log _- Real.log _=Real.log _; let v:= W i j y; let u:= U i j y; change Real.log v-Real.log u=Real.log (1+(v-u)*u⁻¹); have hv: 0<v:= ht; have hx:0<u:= hy; rw [← Real.log_div hv.ne' hx.ne',show 1+(v-u)*u⁻¹=v/u from by field_simp; ring]
lemma concordance (h:Word N x k n p U T)(hv:Word N x k n p W P)(he:∀ᶠ i in atTop,∀ j,j≤n → T j i=P j i) : Budget N x k (p*(n+1)) (U-W) := by
    refine Arms.confirm (h:=?_ ) (Arms.sub h.grade hv.grade); filter_upwards [he] with i hi; funext x y; simp only [Pi.sub_apply,green, Finset.sum_apply]; rw [show (∑ j∈Finset.range (n+1), T j i x y)=∑ j∈Finset.range (n+1),P j i x y from Finset.sum_congr rfl (fun j hj=>congr_fun (congr_fun (hi j (Nat.le_of_lt_succ (mem_range.mp hj))) x) y)]; abel
end Capture
end
end YM.Contacts.Loom
