import YM.LocalLTE.Units.Grove
/-! Orbits local coordinate. Use finite-rank axial chart in complete supports. Including chord thresholds. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} {o q : Site c} {m:ℕ}
namespace Grove
variable (X:Grove o)
def fits (i:Bond c) (o:Site c) (m:ℕ):Prop:=i.1∈neighbors m o ∧ i.1+step i.2∈neighbors m o
def Spare (m:ℕ)(i:Bond c) := fits i o m ∧ ¬ X.Twig m i
-- Fibre on complete links. Keep continuous through all masks.
def shore (m:ℕ):Directions G c →L[ℝ] Directions G c:= ContinuousLinearMap.pi (fun i=> if X.Spare m i then ContinuousLinearMap.proj i else 0)
lemma shore_apply (m:ℕ)(v: Directions G c) (i): X.shore m v i = if X.Spare m i then v i else 0 := by
  unfold shore; by_cases hi:X.Spare m i <;>simp only [hi, ↓reduceIte, ContinuousLinearMap.pi_apply]
  all_goals rfl
lemma norm_shore (m:ℕ) (v:Directions G c) : ‖X.shore m v‖≤‖v‖:= by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro i; rw [shore_apply]; split
  · exact norm_le_pi_norm ..
  simp

def crook (m:ℕ)(χ:Chi)(d:ℝ)(V:Config G c) : Directions G c := X.shore m (fun i:Bond c=> cutLog χ d (X.fix V i))
lemma lark (V U:Config G c)(h:Agrees (neighbors m o:Set (Four (Per c))) V U)(χ:Chi)(d:ℝ): X.crook m χ d V=X.crook m χ d U:= by
  funext i; unfold crook; rw [shore_apply,shore_apply]; split; next hV=> rw [X.fixes h _ hV.1.1 hV.1.2]
  rfl
lemma range_id (m:ℕ)(f:Directions G c): X.shore m (X.shore m f)=X.shore m f:= by
  funext i; conv_lhs=> rw [shore_apply]
  split;  rfl; rw [shore_apply,if_neg (by assumption)]
-- No estimate on WIND exterior under polynomial! Cost only Healthy germs.
def soloV (x:Directions G c) : Config G c:=fun i=> G.lieExp (x i)
lemma repairs {d γ:ℝ}(χ:Chi)(h: Reliable G d γ)(V : Config G c)(he:∀ i,X.Spare m i→ G.chord (X.fix V i) ≤ d): Agrees (neighbors m o:Set (Four (Per c))) (soloV (X.crook m χ d V)) (X.fix V):=by
  intro i hz hv; unfold soloV crook; rw [shore_apply]; split
  next hi=> rw [h.kept _ _ (he i hi)]; exact h.right _ ((he i hi).trans (by have he:=h.down; linarith))
  next hi=> obtain ⟨y,ht,hM,hf⟩:= not_not.mp (mt (And.intro (show fits i o m from ⟨hz,hv⟩)) hi); rw [← hf,G.mat_lieExp_zero,X.edge]

lemma adjust (k:ℕ)(x: Directions G c) (i : Bond c)(h:X.Twig k i) : soloV (X.shore k x) i=1:= by
  unfold soloV; rw [shore_apply,if_neg (fun he=> he.2 h),G.mat_lieExp_zero]

lemma sampled {k d e:ℝ}(χ: Chi)(hp: Reliable G d k) (h:∀ x:G.Color,‖x‖≤e→ G.chord (G.lieExp x)≤d∧ G.plog (G.mat (G.lieExp x))=x)
    (v : Directions G c) (he: ‖v‖ ≤ e) (m:ℕ): X.crook m χ d (soloV (X.shore m v))=X.shore m v:= by
  set S:= soloV (X.shore m v); funext i; unfold crook; rw [shore_apply,shore_apply]; split; swap; · rfl
  next hi=>
    have hp':X.fix S i=S i:= by unfold fix Lattice.gauge; rw [fixed _ (X.adjust _ _) _ hi.1.1,fixed _ (X.adjust _ _) _ hi.1.2]; group
    rw [hp', show S i=G.lieExp (v i) from by unfold S soloV; rw [shore_apply,if_pos hi]]
    obtain ⟨he,hz⟩:=h (v i) ((norm_le_pi_norm ..).trans he); rw [hp.kept _ _ he,hz]

lemma cost_travel (U:Config G c) (x:ℝ)(hu:∀ i,G.chord (U i)≤x) (l:Walk) (o:Site c): G.chord (Lattice.travel U o l)≤ l.length*x:= by
  induction l generalizing o with
  | nil=> simp [Lattice.travel]
  | cons i l h=>
    have he : G.chord (i.read U o)≤x:= by unfold Step.read; split; rw [G.chord_inv]; exact hu _; exact hu _
    unfold Lattice.travel; rw [List.length_cons]; apply (G.chord_triangle ..).trans ((add_le_add he (h _)).trans ?_); exact le_of_eq (by push_cast; ring)
lemma sound_ball (G:Gauge){χ:Chi}{k d:ℝ}(h:Reliable G d k):∃ s:ℝ,0<s ∧ ∀ (c:Side)(p:BudgetPoint)(o:Site c)(X:Grove o)(m:ℕ) (v: Directions G c), ‖v‖ ≤ s*p.threshold →
      let U:= soloV (X.shore m v); X.crook m χ d U=X.shore m v∧ Healthy p.threshold univ U := by
  obtain ⟨A,δ,hA,hδ,hB⟩:= chord_chart_cost G
  obtain ⟨K,hK,hX⟩:= Metric.mem_nhds_iff.mp G.plog_left -- ball
  let s:= min (min δ (K/2)) (min (d/A) (1/(4*A)))
  have he:s≤δ:= (min_le_left ..).trans (min_le_left ..); have hr: s<K:= lt_of_le_of_lt (le_trans (min_le_left ..) (min_le_right ..)) (half_lt_self hK)
  have ht:A*s ≤ d:=mul_comm A s ▸ (le_div_iff₀ hA).1 ((min_le_right ..).trans (min_le_left ..))
  have hp':s*(4*A)≤1:= (le_div_iff₀ (by positivity)).1 ((min_le_right ..).trans (min_le_right ..))
  have hs:0<s:= lt_min (lt_min hδ (half_pos hK)) (lt_min (div_pos h.down hA) (by positivity))
  refine ⟨s,hs,?_⟩; intro c p o X m v hv U
  have hf:=p.threshold_pos; have hu:s*p.threshold ≤ s:=mul_le_of_le_one_right hs.le p.threshold_le
  refine ⟨X.sampled χ h (fun i hi=> ?_) _ (hv.trans hu) _, Finset.disjoint_left.mpr ?_⟩
  · refine ⟨(hB _ (hi.trans he)).trans ((mul_le_mul_of_nonneg_left hi hA.le).trans ht), hX (mem_ball_zero_iff.mpr (hi.trans_lt hr))⟩
  intro i _ hx; obtain ⟨y,_,hy⟩:= (flags_spec ..).mp hx; apply hy.not_ge
  have ht i : G.chord (U i) ≤ A*(s*p.threshold):= by
    have he': ‖X.shore m v i‖≤ s*p.threshold := (norm_le_pi_norm ..).trans ((X.norm_shore _ v).trans hv)
    exact (hB _ (he'.trans (hu.trans he))).trans (mul_le_mul_of_nonneg_left he' hA.le)
  refine (cost_travel U _ ht (Lattice.square y.2.val.1 y.2.val.2) y.1).trans ?_; change (↑(4:ℕ):ℝ)*_ ≤_; push_cast; linarith only [mul_le_mul_of_nonneg_right hp' hf.le]
end Grove
end YM.LocalLTE.FrameBox
