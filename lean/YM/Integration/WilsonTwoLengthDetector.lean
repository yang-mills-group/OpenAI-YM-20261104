import YM.Integration.WilsonMovingFarShell

/-! Both physical scales may shrink on the original finite detector, with one
entrance valid for all its rows and all admissible inner locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTwoLengthDetector
open Set Filter Function Spec OPE OPE.Orbits PhysMS Trace.Pilot
open WilsonMovingFarShell
open scoped Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S)
local notation "S₀" => Climb.Bel C.book

private theorem apt (τ : ℝ) (hτ : 0 < τ) (e : ExteriorData S₀) (he : Apt e) :
    Apt (WilsonFarShell.exterior J τ e) := by
  let x := Points.cons 0 (τ • OPE.positions S₀ e)
  have hx : x ∈ generic _ := by
    rw [show x = τ • Points.cons 0 (OPE.positions S₀ e) by
      simp only [x, Work.A05.smul_cons, smul_zero]]
    intro a i j hij
    exact he a (mul_left_cancel₀ hτ.ne' (by simpa only [PiLp.smul_apply, smul_eq_mul] using hij))
  have h := OPE.classes_apt (S := S) x hx (WilsonExteriorPortfolio.carried J τ ∘ OPE.tags S₀ e)
  have hy : Points.tail (Points.across (-(x 0)) x) = τ • OPE.positions S₀ e := by
    apply PiLp.ext
    intro i
    change (τ • OPE.positions S₀ e) i + -(0 : E4) = _
    simp
  rw [hy] at h
  exact h

variable {I : Type} [Fintype I] {d : I → ℕ}
include F in
private theorem placed (τ : ℝ) (e : ExteriorData S₀) (x : I → E4) (v : Labels S d)
    (hx : Injective (beside x (τ • OPE.positions S₀ e).ofLp)) :
    let u := WilsonFarShell.exterior J τ e
    whole S x v (OPE.positions S u).ofLp
        (e := fun j => (OPE.tags S u j).1) (fun j => (OPE.tags S u j).2) =
      whole S x v (τ • OPE.positions S₀ e).ofLp
        (e := fun j => (OPE.tags S₀ e j).1) (Frame.born J τ (fun j => (OPE.tags S₀ e j).2)) := by
  intro u
  let q : Fin u.length ≃ Fin e.length := finCongr (by simp [u, WilsonFarShell.exterior, classes])
  let a := Equiv.sumCongr (Equiv.refl I) q
  have coord (i : Fin u.length) : (OPE.positions S u) i = (τ • OPE.positions S₀ e) (q i) := by
    change (u.get i).1 = _
    rw [show u.get i = ((τ • OPE.positions S₀ e) (q i),
      WilsonExteriorPortfolio.carried J τ (OPE.tags S₀ e (q i))) from List.get_ofFn ..]
  have mark (i : Fin u.length) : OPE.tags S u i =
      WilsonExteriorPortfolio.carried J τ (OPE.tags S₀ e (q i)) := by
    change (u.get i).2 = _
    rw [show u.get i = ((τ • OPE.positions S₀ e) (q i),
      WilsonExteriorPortfolio.carried J τ (OPE.tags S₀ e (q i))) from List.get_ofFn ..]
  rw [whole_observed,whole_observed]
  have position : beside x (OPE.positions S u).ofLp =
      beside x (τ • OPE.positions S₀ e).ofLp ∘ a := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact coord i
  have tag : beside (names v) (names (S := S) (d := fun j => (OPE.tags S u j).1)
        (fun j => (OPE.tags S u j).2)) =
      beside (names v) (names (Frame.born J τ (fun j => (OPE.tags S₀ e j).2))) ∘ a := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact congrArg (detectorRaw S) (mark i)
  rw [position,tag]
  exact perm_observe S F.room.kernel.laws.toSymmetric a _ hx

private theorem clearance {K E : Type} [Fintype E] {l : Filter K} {A : K → ℝ}
    (hA : Tendsto A l atTop) (b : ℝ) (z : E → E4) {δ : ℝ} (hδ : 0 < δ)
    (clear : ClearOf 0 z δ) :
    let Y := fun i j => length b (A i) • z j
    Intervals l A b (fun _ => sole (0 : E4)) Y ∧ Kept l A b Y := by
  intro Y
  have gap (c : ℝ) (hc : b < c) : ∀ᶠ i in l, Real.exp (-c*A i) < δ*length b (A i) :=
    ((RateIs.const hA hδ).mul (RateIs.exp (-b) hA)).overtakes
      (RateLE.exp (-c) hA) hA (by linarith)
  have separation (x y : E4) (i : K) :
      ‖length b (A i) • x-length b (A i) • y‖ = length b (A i)*‖x-y‖ := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<length b (A i) from Real.exp_pos _)]
  constructor
  · intro c hc
    filter_upwards [gap c hc] with i hi _ j
    have own := mul_le_mul_of_nonneg_left (clear.openSpace j) (Real.exp_nonneg (-b*A i))
    simpa only [sole, Y, smul_zero, mul_comm δ (length b (A i))] using
      (hi.trans_le ((mul_comm δ (length b (A i))) ▸ own)).trans_eq (separation 0 (z j) i).symm
  · intro c hc
    filter_upwards [gap c hc] with i hi j k h
    exact ((hi.trans_le ((mul_comm δ (length b (A i))) ▸
      mul_le_mul_of_nonneg_left (clear.spread j k h) (Real.exp_nonneg (-b*A i))))).trans_eq
      (separation (z j) (z k) i).symm

variable (H : Leading F J) (services : Services C f S)
    (v : (i : I) → (Climb.Bel C.book).Field (d i))

include H services in
/-- Simultaneous original measured rows, with actual inner sites chosen after the clock.
The two true lengths are `r=e^(−L)` and `τ=e^(−bL)`, for each fixed `0<b<1`. -/
theorem measured {h : ℕ} (E : Detector S₀ h) {b M η ζ : ℝ} (hb : 0 < b) (hb' : b < 1)
    (hM : 0 ≤ M) (hη : 0 < η) (hζ : ζ < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ x : I → E4, WithinRoom (length 1 L) M η x 0 →
      ‖WilsonFarShell.readings J v E (length b L) (length 1 L) x -
        WilsonExteriorPortfolio.bank J E S (length b L) (((J (length b L) h).symm)
          (J (length 1 L) h (WilsonFarShell.coefficient F R J v h (length 1 L) x)))‖ ≤
        (length 1 L/length b L)^((h:ℝ)+ζ) := by
  apply refine_geometry
  intro X l hl sub room
  haveI := hl
  have time : Tendsto (fun i : ℝ => i) l atTop := tendsto_id.mono_left sub
  have hr : Tendsto (fun i : ℝ => length 1 i) l trail :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by norm_num : -(1:ℝ)<0) time),
      Eventually.of_forall (fun _ => Real.exp_pos _)⟩
  have inroom := room_regime hr hM hη room
  simp only [run,length,Real.log_exp,neg_one_mul,neg_neg] at inroom
  choose δ hδ able using fun j => detector_exterior_clearance (E.listen j) (E.awake j)
  have each (j : Fin E.size) :
      ∀ᶠ L in l, ‖WilsonFarShell.readings J v E (length b L) (length 1 L) (X L) j -
        WilsonExteriorPortfolio.row J S (length b L) h (E.listen j)
          ((J (length b L) h).symm (R.packet h (X L) (Frame.born J (length 1 L) v) 0))‖ ≤
        (length 1 L/length b L)^((h:ℝ)+ζ) := by
    let e := E.listen j
    let w := fun j => (OPE.tags S₀ e j).2
    let y := fun i => (length b i • OPE.positions S₀ e).ofLp
    have geo := clearance time b (OPE.positions S₀ e).ofLp (hδ j) (able j)
    have disjoint := clearance_both time inroom.1 inroom.2 geo.1 geo.2 hb' (le_refl b)
    have result := separated F R J H services time hb hb' inroom.1 inroom.2 geo.1 geo.2
      (fun _ => none) h v w hζ
    filter_upwards [result,disjoint.1,disjoint.2] with L paid center full
    let u := Frame.born J (length 1 L) v
    let z := R.packet h (X L) u 0
    let τ := length b L
    rw [← WilsonFarShell.measured_row J]
    change ‖whole _ _ _ _ _ - _‖ ≤ _
    rw [placed F J τ e (X L) u full, detector_witness_eq_upon F _ (apt J τ (Real.exp_pos _) e
      (E.awake j))]
    change ‖_ - whole _ _ _ _ _‖ ≤ _
    rw [placed F J τ e (sole (0 : E4)) (sole z : Labels S (fun _ : Unit => h)) center]
    change ‖whole S (X L) u (y L) (Frame.born J τ w) -
      trunc S F R h (X L) 0 u (y L) (Frame.born J τ w)‖ ≤ _ at paid
    have read := packet_read F R (X L) (0 : E4) u (y L) (Frame.born J τ w) none h center
    change upon S h 0 (y L) (Frame.born J τ w) z =
      trunc S F R h (X L) 0 u (y L) (Frame.born J τ w) at read
    rw [← read] at paid
    exact paid
  refine ⟨l,hl,le_rfl,?_⟩
  filter_upwards [eventually_all.mpr each] with L hl
  apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg
    (div_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) _)).mpr
  intro j
  change ‖WilsonFarShell.readings J v E (length b L) (length 1 L) (X L) j -
    WilsonExteriorPortfolio.row J S (length b L) h (E.listen j) _‖ ≤
      (length 1 L/length b L)^((h:ℝ)+ζ)
  simpa only [WilsonFarShell.coefficient,LinearEquiv.apply_symm_apply] using hl j

end YM.Integration.WilsonTwoLengthDetector
