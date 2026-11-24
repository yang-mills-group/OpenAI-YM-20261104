import YM.Integration.WilsonMacroscopicForwardTransfer
import YM.Integration.WilsonMacroscopicRichCaptureRoots

/-! A common coarse-cell translation of every physical ultraviolet mark
preserves the actual flat conditioned response on the same Wilson period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFlatTranslation
open Function Finset Filter MeasureTheory Lattice RG Wilson Source Push.GridApprox OPE OPE.Therm
open PhysicalNext.Repeat.Legato WilsonMacroscopicForwardTransfer
open private admissible from YM.Integration.WilsonMacroscopicForwardTransfer
open scoped Classical BigOperators Topology
variable {G : Gauge}

private theorem step (H : History G) (N p m : ℕ) (q : Site (H.S.side m p))
    (X : Config G (H.S.side (m+1) p) → ℂ) (hx : Integrable X (prior G _)) :
    let S := H.levels.clock.op m p
    let β := H.β N p (m+1)
    S.push β (X ∘ pull 1 (S.ratio.embed q)) = (S.push β X) ∘ pull 1 q := by
  intro S β
  funext V
  let move := pull 1 (S.ratio.embed q) (K := G.El)
  let Y := fun U : Config G (H.S.side (m+1) p) => S.density β U (pull 1 q V) • X U
  have hk : S.IsKernel β G := H.levels.transition_mass m p β
  have hi : Integrable Y (prior G _) := StepData.push_slice hk _ X hx
  have hmove : MeasurePreserving move (prior G _) (prior G _) := prior_pull ..
  have change := integral_map (μ:=prior G _) (φ:=move) (f:=Y) hmove.aemeasurable (by rw [hmove.map_eq]; exact hi.aestronglyMeasurable)
  rw [hmove.map_eq] at change
  change (∫ U, S.density β U V • X (move U) ∂prior G _) = ∫ U, Y U ∂prior G _
  rw [change]
  apply integral_congr_ae
  exact ae_of_all _ fun U => congrArg (· • X (move U)) ((H.levels.blocks m p).symmetric β U V 1 q).symm

theorem pushed (H : History G) (N p : ℕ) {b m : ℕ} (bm : b ≤ m) (q : Site (H.S.side b p)) :
    ∀ (X : Config G (H.S.side m p) → ℂ), Integrable X (prior G _) →
      pushTo H N p bm (X ∘ pull 1 (anchor H.S p bm q)) = (pushTo H N p bm X) ∘ pull 1 q := by
  induction m, bm using Nat.le_induction with
  | base =>
    intro X hx
    have here : anchor H.S p (le_rfl : b ≤ b) q = q := by
      unfold anchor Ratio.embed Schedule.toDepth
      simp only [tsub_self,Schedule.steps]
      rw [show ((1:Side).val:ℕ)=1 from rfl,one_smul,wrap_lift]
    simp [here]
  | succ m bm ih =>
    intro X hx
    rw [pushTo_next H N p bm, pushTo_next H N p bm, ← anchor_next H.S p bm]
    have first := congrArg (pushTo H N p bm) (step H N p m (anchor H.S p bm q) X hx)
    exact first.trans (ih _ (StepData.push_integrable (H.levels.transition_mass ..) X hx))

private theorem numerator (R : Run G) (N p : ℕ) (q : Site (R.family.side N p)) (X : Config G (R.family.side N p) → ℂ) :
    weighted (C := R.family) (N := N) (X ∘ pull 1 q) = (weighted (C := R.family) (N := N) X) ∘ pull 1 q := by
  funext U
  have top : (R.family.path.rep N p N).eval = bare (R.family.path.β N p N) := (R.makes.wilson.starts N p).2
  change (((R.family.path.rep N p N).eval U / _ : ℝ) : ℂ)*X (pull 1 q U) =
    (((R.family.path.rep N p N).eval (pull 1 q U) / _ : ℝ) : ℂ) * X (pull 1 q U)
  rw [top,bare_pull]

/-- Full positive physical denominator and signed numerator at these finer
    sites on the existing coarse chart. The preimage shift is the exact
    integer embedding of the given coarse torus, for every retained period. -/
theorem held (R : Run G) {b N p : ℕ} (bN : b ≤ N) (q : Site (R.family.side b p))
    (X : Config G (R.family.side N p) → ℂ) (hx : Integrable X (scene R.family.path N p N)) :
    exterior (C := R.family) (N := N) bN (X ∘ pull 1 ((R.family.S.toDepth bN p).embed q)) 1 =
      exterior (C := R.family) (N := N) bN X 1 := by
  unfold exterior
  rw [numerator]
  have h := congrFun (pushed R.family.path N p bN q _ ((admissible R.makes (le_rfl : N ≤ N) X).mp hx)) (1 : Config G (R.family.side b p))
  have one : pull 1 q (1 : Config G (R.family.side b p)) = 1 := by rw [pull_one]; rfl
  rw [comp_apply,one] at h
  exact congrArg (fun z : ℂ => z / _) h

/-- A heterogeneous two-point assay and its separated signed partners are all
    translated together. This includes the actual subtraction of a fixed
    measured vacuum mean at every marked seat. -/
theorem roster (R : Run G) {b N p : ℕ} (bN : b ≤ N) {I : Type} [Fintype I] (h : I → ℕ)
    (v : (j : I) → R.family.label (h j)) (x : I → Site (R.family.side N p)) (center : I → ℂ)
    (q : Site (R.family.side b p)) :
    let Q := (R.family.S.toDepth bN p).embed q
    exterior (C := R.family) (N := N) bN (fun U => ∏ j, (R.family.O N p (v j) (x j+Q) U-center j)) 1 =
      exterior (C := R.family) (N := N) bN (fun U => ∏ j, (R.family.O N p (v j) (x j) U-center j)) 1 := by
  intro Q
  let X := fun U : Config G (R.family.side N p) => ∏ j, (R.family.O N p (v j) (x j) U-center j)
  have cont : Continuous X := continuous_finsetProd _ fun j _ => (R.family.continuousO N p (h j) (v j) (x j)).sub continuous_const
  letI : IsProbabilityMeasure (scene R.family.path N p N) := probability R.makes.wilson le_rfl
  have hi : Integrable X (scene R.family.path N p N) := (Envelope.compactC cont).integrableC _
  have shift : (fun U => ∏ j, (R.family.O N p (v j) (x j+Q) U-center j)) = X ∘ pull 1 Q := by
    funext U
    simp only [comp_apply,pull_one,X,R.family.translation]
  rw [shift]
  exact held R bN q X hi

end YM.Integration.WilsonMacroscopicRichFlatTranslation
