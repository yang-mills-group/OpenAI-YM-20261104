import YM.Pert.Flow.Strain
/-! Piecewise affine interpolation in log inverse spacing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.Pert.Flow
open Function Filter Topology Set Extraction Asymptotics
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {F : Order}
variable (P : Strain C F)

lemma increasing_clock : StrictMono C.S.scale := by
   apply strictMono_nat_of_lt_succ
   intro i
   have h:= stride_pos (C:=C) i
   rw [C.S.scale_succ]; unfold logStride at h; linarith

private lemma border_obtained (t:ℝ) : ∃ j:ℕ, t < C.S.scale j := ((C.S.divergent.eventually_gt_atTop t).exists).imp fun _ hx=> hx

/-- Left endpoint index (right interval chosen at a shared endpoint; edge clamps would lead to different continuation near `μ=1` only). -/
def windowIndex (C : Family G) (t:ℝ) := Nat.find (border_obtained (C:=C) t)-1
lemma locates {t:ℝ} (ht : 0 ≤ t) : t∈ Ico (C.S.scale (windowIndex C t)) (C.S.scale (windowIndex C t+1)) := by
   let n:=Nat.find (border_obtained (C:=C) t)
   have h:=Nat.find_spec (border_obtained (C:=C) t)
   have h : t  <  C.S.scale n := h
   have he : n≠ 0 := by rintro he; rw [he,C.S.scale_zero] at h; exact ht.not_gt h
   have hn : ¬t < C.S.scale (n-1) := Nat.find_min (border_obtained (C:=C) t) (show _  <  _ from by omega)
   change _ ≤  _ ∧ _  <  _
   change C.S.scale (n-1)  ≤  t ∧ _  <  _
   exact ⟨not_lt.1 hn,(show windowIndex C t+1 = n from (by change n-1+1=n;omega)) ▸ h⟩
lemma index_ascends : Tendsto (windowIndex C) atTop atTop := by
   refine tendsto_atTop.2 fun i=>?_ 
   filter_upwards [eventually_ge_atTop (C.S.scale i),eventually_ge_atTop 0] with t ht h
   have h : C.S.scale i  <  C.S.scale (windowIndex C t+1) := lt_of_le_of_lt ht ((locates (C:=C) h).2)
   exact Nat.lt_succ_iff.mp ((increasing_clock.lt_iff_lt.mp h))
lemma index_order {s t:ℝ} (ht:0 ≤ s) (hv:s ≤ t) : windowIndex C s  ≤  windowIndex C t := by
   have h := locates (C:=C) ht
   have h' := locates (C:=C) (ht.trans hv)
   exact Nat.lt_succ_iff.mp  <| increasing_clock.lt_iff_lt.mp  <| lt_of_le_of_lt h.1  <| lt_of_le_of_lt hv h'.2

def line (i : ℕ) (t : ℝ) :=
   P.β i + (P.β (i+1)-P.β i)/logStride C i * (t-C.S.scale i)
def interpolated : ℝ→ℝ := fun t=> line P (windowIndex C t) t
 -- note field notation
lemma line_anchors (i) : line P i (C.S.scale i)= P.β i ∧ line P i (C.S.scale (i+1))=P.β (i+1) := by
   constructor
   · simp [line]
   have hl:=C.S.scale_succ i
   have hz:= stride_pos (C:=C) i
   dsimp [line,logStride] at *
   rw [hl]; field_simp; ring

lemma high_step_prices {ε : ℝ} (hε : 0 < ε) : ∃ j, ∀ i, j ≤ i → |(P.β (i+1)-P.β i)/logStride C i - 2*b0 G|  ≤  ε := by
   obtain ⟨j,hj⟩:= eventually_atTop.mp (drift_price (C:=C)|>.eventually (gt_mem_nhds hε))
   refine ⟨j,fun i hi=> ?_⟩
   have hv := stride_pos (C:=C) i
   have he:=P.step i
   rw [show ((P.β (i+1)-P.β i)/logStride C i - 2*b0 G)=(P.β (i+1)-P.β i-2*b0 G*logStride C i) / logStride C i from by
      field_simp, abs_div,abs_of_pos hv]
   exact (div_le_div_of_nonneg_right he hv.le).trans (le_of_lt (hj i hi))

lemma secant_call {ε : ℝ} (hε : 0 < ε) :
   ∀ᶠ t : ℝ in atTop, ∀ u:ℝ, t  ≤  u → |interpolated P u - interpolated P t - 2*b0 G * (u-t)|  ≤  ε * (u-t) := by
   obtain ⟨m,H⟩:= high_step_prices P hε
   filter_upwards [index_ascends (C:=C) |>.eventually_ge_atTop m,eventually_ge_atTop 0] with t hm ht u hu
   have he (i) (hi: m  ≤  i) (a b:ℝ) (hb:a ≤ b) : |line P i b-line P i a-2*b0 G*(b-a)|  ≤  ε *(b-a) := by
      have hx := mul_le_mul_of_nonneg_right (H i hi) (show 0  ≤  b-a from sub_nonneg.2 hb)
      rwa [show _-_ - _= (((P.β (i+1)-P.β i)/logStride C i - 2*b0 G))*(b-a) from (by dsimp [line];ring), abs_mul, abs_of_nonneg (sub_nonneg.2 hb)]
   let i:=windowIndex C t; let j:=windowIndex C u
   have hi := index_order (C:=C) ht hu
   have hC i : C.S.scale i  ≤  C.S.scale (i+1) := increasing_clock.monotone (Nat.le_succ _)
   change i ≤ j at hi
   rcases lt_or_eq_of_le hi with hi|hi
   · have hf (j) (h:i+1  ≤  j) : |P.β j-P.β (i+1) - 2*b0 G*(C.S.scale j-C.S.scale (i+1))|  ≤  ε*(C.S.scale j-C.S.scale (i+1)):= by
         induction j,h using Nat.le_induction with
         | base => simp
         | succ k h ih =>
            have hh:=he k ((hm.trans (Nat.le_succ _)).trans h) _ _ (hC k); obtain ⟨ha,hb⟩:= abs_le.mp hh; obtain ⟨hc,hd⟩:=abs_le.mp ih
            rw [(line_anchors P _).1,(line_anchors P _).2] at ha hb
            exact abs_le.mpr ⟨by linarith,by linarith⟩
     have h':=he i hm _ _ (locates (C:=C) ht).2.le
     have h'':=he j (hm.trans hi.le) _ _ (locates (C:=C) (ht.trans hu)).1
     have hl := hf j hi
     rw [(line_anchors P _).2] at h'
     rw [(line_anchors P _).1] at h''
     change |line P j u - line P i t - _|  ≤  _
     simp only [abs_le] at hl h' h''
     exact abs_le.mpr ⟨by linarith,by linarith⟩
   have hh:=congr_arg (fun w=>line P w u) hi
   change |line P j u-line P i t-_| ≤ _
   rw [←hh]; exact he i hm t u hu

end YM.Pert.Flow
