import YM.Pert.Scale.Roll
/-! Definition of actual relative position frame in length units. All corrections computed on common actual witness. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Pert.Scale
open Extra.FD RawLabels Maxwell Filter Topology Set Function Analysis Spec Ward Climb Position Labels Rigid
open scoped Topology ContDiff
variable {G:Gauge} {C:Family G} {I:Extraction.Order} {S:Table C.book} {d n : ℕ}

lemma gear_chain (F : Frames G) {d : ℕ} (s t : ℝ) (v : E F d) : gear F d s (gear F d t v)=gear F d (s*t) v := by
  let B := recorded F d
  have h := B.b.sum_equivFun v
  rw [← h]
  simp only [map_sum,map_smul,rare, Complex.ofReal_mul,mul_pow,mul_smul]
  apply Finset.sum_congr rfl; intro i _
  rw [smul_comm ((t:ℂ)^(B.w i).1) ((s:ℂ)^(B.w i).1)]

lemma gear_inverse (F : Frames G) {d} {s : ℝ} (hs:s≠0) (v : E F d) : gear F d s⁻¹ (gear F d s v)=v := by
  rw [gear_chain,inv_mul_cancel₀ hs,←motor_bank F v 1,bank_origin]
  unfold motor; change v+(0:Position.operator F d) v=_; rw [ContinuousLinearMap.zero_apply,add_zero]

lemma gear_whole {d : ℕ} (F : Frames G) {t : ℝ} (hn : t≠0) : Bijective (gear F d t) := by
  have hs (x : E F d) : gear F d t (gear F d t⁻¹ x)=x := by
    have hf := gear_inverse F (s:=t⁻¹) (inv_ne_zero hn) (d:=d) x
    rw [_root_.inv_inv t] at hf
    exact hf
  exact ⟨LeftInverse.injective (f:=gear F d t) (g:=gear F d t⁻¹) (gear_inverse F hn),fun x=>⟨gear F d t⁻¹ x,hs x⟩⟩
set_option maxHeartbeats 700000 in
lemma cmotor_whole {d : ℕ} (F : Frames G) (v : Buffer F d) (hp : IsUnit (motor F v)) : Bijective (cmotor F v) :=
     show Bijective (motor F v) from ContinuousLinearMap.isUnit_iff_bijective.mp hp

lemma total_internal {d : ℕ} (F : Frames G) (t : ℝ) (v : Buffer F d) (hp : 0<t ∧ IsUnit (motor F v)) :
   Bijective (gear F d t : E F d→E F d) ∧ Bijective (cmotor F v : E F d→E F d) :=
     ⟨gear_whole F hp.1.ne',cmotor_whole F _ hp.2⟩
def gearIso (F : Frames G) (d : ℕ) (t) (ht : (0:ℝ)<t) : E F d ≃ₗ[ℂ] E F d := LinearEquiv.ofBijective (gear F d t) (gear_whole F ht.ne')
def motIso (F : Frames G) (d : ℕ) (v : Buffer F d) (h : IsUnit (motor F v)) : E F d ≃ₗ[ℂ] E F d := LinearEquiv.ofBijective (cmotor F v) (cmotor_whole F v h)

variable (X : Scaling S) {Q : Conditions C.labels d n} {φ : Ledger Q → Buffer C.labels d}
def correction (φ : Ledger Q → Buffer C.labels d) (k) (t) := φ (rolled Q X k t)
def Cleared (φ : Ledger Q → Buffer C.labels d) (k) (t) := 0 < t ∧ IsUnit (motor C.labels (correction X φ k t))
open scoped Classical in
def relative (X : Scaling S) (φ : Ledger Q → Buffer C.labels d) (k : ℕ) (t : ℝ) : E C.labels d ≃ₗ[ℂ] E C.labels d := if h : Cleared X φ k t then
    (motIso C.labels d _ h.2).trans (gearIso C.labels d t h.1) else LinearEquiv.refl _ _
def positionScale (φ : Ledger Q → Buffer C.labels d) (k : ℕ) (t : ℝ) := (relative X φ k t).trans (X.U k d)
lemma rel_eq {k t} (hv : Cleared X φ k t) (p) : relative X φ k t p = gear C.labels d t (motor C.labels (correction X φ k t) p) := by unfold relative; rw [dif_pos hv]; rfl
lemma pos_eq {k t} (hv : Cleared X φ k t) (p) : positionScale X φ k t p=X.U k d (gear C.labels d t (motor C.labels (correction X φ k t) p)) := by rw [positionScale,LinearEquiv.trans_apply,rel_eq X hv]

variable {X} {b : Final C I S} (h : FirstExtension b X) (hv : CleanProfiles Q) (hl : Reports (chart Q) (white Q) 0 φ)
include hv h hl
theorem corrects {s : ℝ} (hs : 0<s) :
  Tendsto (uncurry (correction X φ)) (atTop ×ˢ 𝓝 s) (𝓝 0) := hl.fixes ▸ hl.diff.continuousAt.tendsto.comp (rolling Q hv h hs)
theorem clearance {s : ℝ} (hs : 0<s) :
  ∀ᶠ q : ℕ×ℝ in atTop ×ˢ 𝓝 s, Cleared X φ q.1 q.2 ∧ chart Q (rolled Q X q.1 q.2,correction X φ q.1 q.2)=chart Q (white Q,0) :=
   (((show ∀ᶠ w : ℝ in 𝓝 s,0<w from lt_mem_nhds hs).prod_inr atTop).and ((corrects h hv hl hs).eventually (invertible_tail C.labels d))).and ((rolling Q hv h hs).eventually hl.curves)
theorem correction_deriv {s : ℝ} (hs : 0<s) :
    (∀ᶠ k in atTop, DifferentiableAt ℝ (correction X φ k) s) ∧ Tendsto (fun k => deriv (correction X φ k) s) atTop (𝓝 0) := by
   have he : Tendsto (fun i : ℕ => (i,s)) atTop (atTop ×ˢ 𝓝 s) := tendsto_id.prodMk tendsto_const_nhds
   have hw := (rolling Q hv h hs) |>.comp he
   have hd := hw.eventually (hl.diff.of_le (show (↑(2:ℕ):WithTop _)≤_ from le_top) |>.eventually (by decide))
   obtain ⟨hT,hR⟩ := rolled_deriv Q hv h hs
   have hf := isBoundedBilinearMap_apply.continuous.continuousAt.tendsto.comp (((hl.diff.continuousAt_fderiv (by decide) |>.tendsto).comp hw).prodMk_nhds hT)
   have hy k (hk : ContDiffAt ℝ (↑(2:ℕ)) φ (rolled Q X k s)) := (hk.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hR k).hasDerivAt
   refine ⟨hd.mono (fun k hk => (hy k hk).differentiableAt),?_⟩
   change Tendsto (fun i : ℕ => fderiv ℝ φ (rolled Q X i s) _) atTop (𝓝 ((fderiv ℝ φ (white Q)) 0)) at hf
   rw [map_zero] at hf
   exact hf.congr' (hd.mono (fun k hk => (hy k hk).deriv.symm))
omit h hv hl

lemma relative_spin {k t} (hg : Cleared X φ k t) (p) (s) : wear C.labels d s (relative X φ k t p)= relative X φ k t (wear C.labels d s p) := by
  rw [rel_eq X hg,rel_eq X hg]; simp only [wear_ride]; rw [gear_spin,motor_spin]
lemma relative_unit {k t} (hg : Cleared X φ k t) :
   relative X φ k t ((freeTable C.labels).unit d)=(freeTable C.labels).unit d := by rw [rel_eq X hg,motor_unit, gear_unit]
lemma relative_lower {k t e} (hg : Cleared X φ k t) (he : e<d) {p} (hp : p∈lower C.labels e d) : relative X φ k t p∈lower C.labels e d := by
   rw [rel_eq X hg]; exact gear_lower _ _ (motor_filter _ he hp) _
lemma position_symmetric {k : ℕ} (he : YM.Spin.realH b.room.kernel.spin (Free.spin_free C.labels) (X.U k d)) {t} (hk : Cleared X φ k t) :
     YM.Spin.realH b.room.kernel.spin (Free.spin_free C.labels) (positionScale X φ k t) := by
  constructor
  · intro s p
    change X.U k d (relative X φ k t (wear C.labels d s p)) = _
    rw [← relative_spin hk]; exact he.1 _ _
  intro p
  rw [pos_eq X hk,pos_eq X hk]
  change X.U k d (gear C.labels d t (motor C.labels _ ((freeTable C.labels).conj (table_spin _) _ p)))=_
  rw [← motor_bar,← gear_conj]
  exact he.2 _

end YM.Pert.Scale
