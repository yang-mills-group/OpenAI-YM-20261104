import YM.Integration.WilsonViewerSignedDictionary
import YM.Integration.WilsonMSDictionarySpatial
import YM.Integration.WilsonMacroscopicDetector

/-! The full separated product at a fixed exterior is measured on the original
finite determining family. Each real or imaginary signed measurement may use
its own cofinal far dates for the independently nominated experiment. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonViewerOriginalProducts
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonMSDictionaryVector WilsonPositionHomogeneousFrame
open WilsonMacroscopicDetector
open private recovered from YM.Integration.WilsonMSDictionarySpatial
open private apart from YM.Integration.WilsonViewerPrescribedPacket
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (simple : G.Simple)
    (lead : Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ k, ∀ᶠ r in trail, Frame.obedient F Y (J r) k)
local notation "P" => homogeneous F J Z
variable {n : ℕ} (d : Fin n → ℕ) (v : (j : Fin n) → RG17.Free R.family (d j))
local notation "arms" => fun r j => P r (d j) (v j)

include lead paid simple in
theorem charges : GradePrice Q d arms (fun _ => 0) := by
  apply WilsonMSDictionaryPositionCost.grades F J Z lead paid simple Q _ d v
  intro k x j
  by_cases hj : j ≤ k
  · have row := Frame.entrust F Q J lead (r:=id) tendsto_id k j hj x
    rw [show LogV ∘ id = OPE.run from funext fun r => by simp [LogV, OPE.run]] at row
    exact row
  · apply RateLE.congr (F:=fun _ : ℝ => (0 : S.Field j)) (RateLE.zero RG17.home OPE.run _)
    exact Eventually.of_forall fun r => (Q.kills_lower j k (Nat.lt_of_not_ge hj) _).symm

variable {σ : Prescription (Press.portDeck G)} {branch : Bool}
    (matchMS : Main.Match Z simple M σ branch) (ν : ℝ) (h q : ℕ) (g : ℝ → ℝ) (ψ : Test n)
local notation "panel" => ((matchMS.separatedOPE ν).wilson.light h).choose
local notation "target" => prediction R.family d h Z M ν v ψ q
local notation "bank" => experiment R.family d h Z M ν v ψ panel q

/-- The measured input uses ordinary whole-product observations on the
unselected original table. All grades of the proposed output use its own
physical public frame. -/
def Rows (a : ℝ → ℝ) : Prop :=
  ∀ᶠ r in trail, 0 ≤ a r ∧ ∀ X : probes F h,
    ∀ χ ∈ ({Complex.reCLM, Complex.imCLM} : Finset (ℂ →L[ℝ] ℝ)),
      ∃ᶠ s : ℝ in atTop,
        |χ (RG17.appeared F (arms r) X.val r ψ -
          X.val.charge F h (P r h (bank (g r) s)))| ≤ a r

include matchMS in
theorem restored (a : ℝ → ℝ) (signed : Rows F J Z M simple d v matchMS ν h q g ψ a) :
    ∀ᶠ r in trail, ‖fromProducts F h (arms r) r ψ - P r h (target (g r))‖ ≤
      ‖restore F h‖ * (2 * a r) := by
  have ready : Read.Detected (Measure.outlook Z.scheme Z.criterion) panel :=
    ((matchMS.separatedOPE ν).wilson.light h).choose_spec.2
  filter_upwards [signed] with r obs
  let u : Labels S d := arms r
  let y := P r h (target (g r))
  let xs (X : probes F h) := RG17.appeared F u X.val r ψ
  let dx := xs - read F h y
  have row (X : probes F h) : ‖dx X‖ ≤ 2 * a r := by
    let L := (X.val.charge F h).toContinuousLinearMap.comp (P r h).toLinearMap.toContinuousLinearMap
    have lim := experiment_limit R.family d h Z M ν v ψ matchMS panel ready q (g r)
    have hL := L.continuous.continuousAt.tendsto.comp lim
    have real (χ : ℂ →L[ℝ] ℝ) (m : χ ∈ ({Complex.reCLM, Complex.imCLM} : Finset (ℂ →L[ℝ] ℝ))) :
        |χ (dx X)| ≤ a r := by
      apply le_of_tendsto_of_frequently (χ.continuous.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x:=xs X)).sub hL)).abs
      exact obs.2 X χ m
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have re := real Complex.reCLM (by simp)
    have im := real Complex.imCLM (by simp)
    change |(dx X).re| ≤ _ at re
    change |(dx X).im| ≤ _ at im
    linarith only [re,im]
  have positive : 0 ≤ 2 * a r := mul_nonneg (by norm_num) obs.1
  have eq : fromProducts F h u r ψ - y = restore F h dx := by rw [map_sub,exact_read]; rfl
  change ‖fromProducts F h u r ψ-y‖ ≤ _
  rw [eq]
  exact ((restore F h).le_opNorm dx).trans (mul_le_mul_of_nonneg_left
    ((pi_norm_le_iff_of_nonneg positive).mpr row) (norm_nonneg _))

variable {E : Type} [Fintype E] {e : E → ℕ} (w : Labels S e) {δ : ℝ} (positive : 0 < δ)

include Q simple lead paid positive in
/-- The signed full ordinary product, against each macroscopic fixed-clearance
spectator, at the same physical positions and calibrated output. -/
theorem full (fac : Facilities R.family f S) (a : ℝ → ℝ)
    (signed : Rows F J Z M simple d v matchMS ν h q g ψ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ (y : E → E4), ClearOf 0 y δ →
      ∀ p : Viewers F, let spatial := r ^ ((h:ℝ)+1-1/4) * ∫ x : Points n, ‖ψ x‖
        ‖RG17.query F (arms r) y w p r ψ - upon (spectator F p) h 0 y w
          (P r h (target (g r)))‖ ≤ spatial + D * (fee F h * spatial + ‖restore F h‖ * (2 * a r)) := by
  have grade := charges F Q J Z simple lead paid d v
  have exactOPE := RG17.testedPacketBound Q fac.toServices arms h (fun _ => 0) grade
    ψ.hasCompactSupport ψ.tsupport_subset (ε:=1/4) (by norm_num) positive w
  have packet := recovered F J Z fac Q d v h ψ grade
  have compared := restored F J Z M simple d v matchMS ν h q g ψ a signed
  obtain ⟨D,Dn,uniform⟩ := WilsonMacroscopicViewerCharge.uniform F fac.toServices h w positive
  refine ⟨D,Dn,?_⟩
  filter_upwards [exactOPE,packet,compared] with r master read price y clear p
  let actual := RG17.basket Q h (arms r) r ψ
  let measured := fromProducts F h (arms r) r ψ
  let output := P r h (target (g r))
  let spatial := r ^ ((h:ℝ)+1-1/4) * ∫ x : Points n, ‖ψ x‖
  have near : ‖RG17.query F (arms r) y w p r ψ - upon (spectator F p) h 0 y w actual‖ ≤ spatial := by
    simpa only [Finset.sum_const_zero, sub_zero] using master ψ (subset_refl _) y clear p
  have rr : ‖actual-measured‖ ≤ fee F h * spatial := by
    rw [norm_sub_rev]
    exact read.trans_eq (mul_assoc ..)
  have crossed : ‖actual-output‖ ≤ fee F h * spatial + ‖restore F h‖ * (2*a r) :=
    (norm_sub_le_norm_sub_add_norm_sub _ measured _).trans (add_le_add rr price)
  have charged := uniform 0 y clear (apart positive clear) p (actual-output)
  rw [map_sub] at charged
  exact (norm_sub_le_norm_sub_add_norm_sub _ (upon (spectator F p) h 0 y w actual) _).trans
    (add_le_add near (charged.trans (mul_le_mul_of_nonneg_left crossed Dn)))


end YM.Integration.WilsonViewerOriginalProducts
end
