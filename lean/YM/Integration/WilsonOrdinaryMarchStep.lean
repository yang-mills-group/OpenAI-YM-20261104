import YM.Integration.WilsonOrdinaryGradedShear

/-! The true adjacent changes of the prescribed frame, on the original RG12
samples. Their canonical shear has unit diagonal and costs only a power of the age. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryMarchStep
open Filter Set Spec Climb OPE RG12 RG12.Frames RG17 SharpGram Trace.Pilot
open WilsonOrdinaryMarchAnchor WilsonOrdinaryGradedShear
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
local notation "V" => Desk.Sector F.sector.derivatives d
local notation "X" => Col V

def engineeringCoord : X ≃ₗ[ℂ] X where
  toLinearMap := dilate (Real.exp 1)
  invFun := dilate (Real.exp 1)⁻¹
  left_inv := scale_cancel (Real.exp_pos _).ne'
  right_inv := scale_cancel' (Real.exp_pos _).ne'

def step (T : X ≃ₗ[ℂ] D) (n : ℕ) : X ≃ₗ[ℂ] X :=
  (((engineeringCoord F d).trans (atSample F J d T (n+1))).trans (atSample F J d T n).symm)

theorem flagged (T : X ≃ₗ[ℂ] D) (O : Prescription F.sector.derivatives) (coh : O.Coherent)
    (align : ∀ᶠ r in trail, triangular V ((Desk.official O coh d).symm.toLinearMap.comp (T.trans (J r d)).toLinearMap)) :
    ∀ᶠ n in atTop, triangular V (step F J d T n).toLinearMap := by
  let Z := atSample F J d T
  let W := Desk.official O coh d
  let U := fun n => (Z n).trans W.symm
  have flag : ∀ᶠ n in atTop, triangular V (U n).toLinearMap := WilsonOrdinaryDyadicAge.approaching.eventually align
  obtain ⟨k,hk⟩ := eventually_atTop.mp flag
  filter_upwards [eventually_ge_atTop k] with n hn
  have idn : (step F J d T n).toLinearMap =
      (U n).symm.toLinearMap.comp ((U (n+1)).toLinearMap.comp (engineeringCoord F d).toLinearMap) := by
    apply LinearMap.ext; intro x
    change (Z n).symm (Z (n+1) (engineeringCoord F d x)) =
      (Z n).symm (W (W.symm (Z (n+1) (engineeringCoord F d x))))
    rw [LinearEquiv.apply_symm_apply]
  rw [idn]; exact (hk n hn).inv.comp ((hk _ (hn.trans (Nat.le_succ n))).comp (tri_dilate _))

private lemma bidirectional {Y U : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ Y] [FiniteDimensional ℂ U]
    (A : Y ≃ₗ[ℂ] U) : ∃ K : ℝ, 0 < K ∧ (∀ y, ‖A y‖ ≤ K*‖y‖) ∧ ∀ u, ‖A.symm u‖ ≤ K*‖u‖ := by
  let u := A.toLinearMap.toContinuousLinearMap
  let v := A.symm.toLinearMap.toContinuousLinearMap
  refine ⟨max 1 (max ‖u‖ ‖v‖),zero_lt_one.trans_le (le_max_left ..),?_,?_⟩
  · intro x; exact (u.le_opNorm x).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (norm_nonneg _))
  · intro x; exact (v.le_opNorm x).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (norm_nonneg _))

private theorem frames (P : Pier.Lair.Present F J) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
    Pier.Lair.Both K (J (Sample.length (n+1)) d) (J (Sample.length n) d) := by
  obtain ⟨j,time,hT,ranges⟩ := Pier.Lair.ranges F P d
  refine ⟨(2*Real.exp 1)^j,by positivity,?_⟩
  have small := (tendsto_nhdsWithin_iff.mp WilsonOrdinaryDyadicAge.approaching).1
  filter_upwards [small.eventually (gt_mem_nhds hT)] with n hn
  obtain ⟨hr,hq,hnext⟩ := Sample.samples_spacing n
  have hp : 0 < Sample.length (n+1) := (Sample.samples_spacing _).1
  have order : Sample.length (n+1) ≤ Sample.length n := hnext.trans_le (div_le_self hr.le hq)
  have factor : 2*Sample.length n / Sample.length (n+1) = 2*Real.exp 1 := by
    rw [hnext,Sample.ratio]; field_simp
  simpa only [factor] using ranges _ _ hp order hn.le

theorem bounded (T : X ≃ₗ[ℂ] D) (P : Pier.Lair.Present F J) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ x : X,
    ‖step F J d T n x‖ ≤ K*‖x‖ ∧ ‖(step F J d T n).symm x‖ ≤ K*‖x‖ := by
  obtain ⟨k,hk,measured⟩ := frames F J d P
  let A := (engineeringCoord F d).trans T
  obtain ⟨c,hc,hA,hA'⟩ := bidirectional A
  obtain ⟨t,ht,hT,hT'⟩ := bidirectional T
  refine ⟨t*k*c,by positivity,?_⟩
  filter_upwards [measured] with n h x
  let before := J (Sample.length n) d
  let after := J (Sample.length (n+1)) d
  have one (v : D) : ‖before.symm (after v)‖ ≤ k*‖v‖ := by
    have tmp : ‖before.symm (after v)‖ ≤ k*‖after.symm (after v)‖ := h.right _
    simpa only [LinearEquiv.symm_apply_apply] using tmp
  have two (v : D) : ‖after.symm (before v)‖ ≤ k*‖v‖ := by
    have tmp : ‖after.symm (before v)‖ ≤ k*‖before.symm (before v)‖ := h.left _
    simpa only [LinearEquiv.symm_apply_apply] using tmp
  constructor
  · change ‖T.symm (before.symm (after (A x)))‖ ≤ _
    calc
      _ ≤ t*(k*(c*‖x‖)) := (hT' _).trans (mul_le_mul_of_nonneg_left
        ((one _).trans (mul_le_mul_of_nonneg_left (hA x) hk.le)) ht.le)
      _ = _ := by ring
  · change ‖A.symm (after.symm (before (T x)))‖ ≤ _
    calc
      _ ≤ c*(k*(t*‖x‖)) := (hA' _).trans (mul_le_mul_of_nonneg_left
        ((two _).trans (mul_le_mul_of_nonneg_left (hT x) hk.le)) hc.le)
      _ = _ := by ring

/-- The specified before- and after-frame change along its true samples fixes
the shear; no assumed shears, inverse prices, or cutoff-dependent choices. -/
def adjustment (T : X ≃ₗ[ℂ] D) (n : ℕ) : X ≃ₗ[ℂ] X :=
  if h : triangular V (step F J d T n).toLinearMap then shear V (step F J d T n) h else LinearEquiv.refl ..

theorem permitted (T : X ≃ₗ[ℂ] D) (P : Pier.Lair.Present F J) (O : Prescription F.sector.derivatives) (coh : O.Coherent)
    (align : ∀ᶠ r in trail, triangular V ((Desk.official O coh d).symm.toLinearMap.comp (T.trans (J r d)).toLinearMap)) :
    ∀ᶠ n in atTop,
    (triangular V (adjustment F J d T n).toLinearMap ∧ ∀ i, ∀ x, block V (adjustment F J d T n).toLinearMap i i x=x) ∧
    (∀ x : X, ‖adjustment F J d T n x‖ ≤ Sample.age n*‖x‖ ∧ ‖(adjustment F J d T n).symm x‖ ≤ Sample.age n*‖x‖) ∧
    ∀ x : X, step F J d T n (adjustment F J d T n x) = diagonalMap V (step F J d T n).toLinearMap x := by
  obtain ⟨K,hK,b⟩ := bounded F J d T P
  have grows : Tendsto Sample.age atTop atTop := tendsto_atTop_mono (fun n=>by unfold Sample.age; linarith) tendsto_natCast_atTop_atTop
  filter_upwards [flagged F J d T O coh align,b,grows.eventually_ge_atTop (K^2)] with n flag cost old
  rw [adjustment,dif_pos flag]
  refine ⟨acts V _ flag,?_,fun x => compensate V _ flag x⟩
  intro x
  have hx := WilsonOrdinaryGradedShear.bounded V _ flag hK.le cost x
  exact ⟨hx.1.trans (mul_le_mul_of_nonneg_right old (norm_nonneg _)),
    hx.2.trans (mul_le_mul_of_nonneg_right old (norm_nonneg _))⟩

end YM.Integration.WilsonOrdinaryMarchStep
