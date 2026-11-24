import YM.Integration.WilsonOriginalDepositedDensity
import YM.Integration.WilsonOriginalDepositedHardRate
import YM.Integration.WilsonPositionThermometerDepositedRow

/-! Hear the actual inverse-fitted cutoff field in the paid signed gallery at the original star. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarSourceIntake
open Function Set Filter MeasureTheory Lattice Wilson RG Source Table Spec Labels Marker QuadraticLocal
open Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.Spindle
open MergeProof.Accent MergeProof.East Extra.Histories
open WilsonOriginalDepositedHard WilsonPositionThermometerDepositedRow
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} (simple : G.Simple) (hc : C.Makes)
variable {f : Extraction.Order} {H : (Bel C.book).Hierarchy}
include simple hc

theorem original (d Q : ℕ) {M ε : ℝ} (margin : 0 < ε) :
    ∀ᶠ k in atTop, ∀ {D : ℕ} (V : Vane C D) (j : Fin (D+1)), j.val=d → V.k=k →
    V.checked f H D → C.ref j ≤ k → ∀ (b : (Bel C.book).Field j), ‖b‖ ≤ M →
    ∀ (N p : ℕ) (upper : k<N),
    let v := V.wheel.atCut (N,p) j b
    let q := row C j k N p v
    let P := C.path.rep N p k
    (C.path.levels.params k).columns ≤ C.path.levels.clock.hatBeta k →
    ∀ {S I T : Type} [DecidableEq S] [Fintype S] {J : Census S}
    {o : S → Site (C.side k p)} (l : S), o l=0 →
    ∀ (old : Gallery T I o P J) (w : S → ℝ) (_positive : ∀ i, 0<w i), w l ≤ 1 →
    ∀ {e E h : ℝ}, 0≤e → old.E.Paid w P.p.B e E →
      old.K.Paid w P.p.B P.p.supportExponent h →
    ∀ (t : T → ℂ), (∀ x, ‖t x‖ ≤ 1) →
    ∃ law : q.Format (o l) C.params P,
      (joined old.K l q law t).Paid w P.p.B P.p.supportExponent
        (h+ε*((C.path.levels.clock.hatBeta k)^Q)⁻¹) ∧
      ∀ x U, (WilsonOriginalDepositedDensity.density old l q law (C.localSection j) t x U).part (J.fire l) -
        (old.density x U).part (J.fire l) = t x *
          (P.eval U • actualTransport C (N:=N) (C.O N p v 0) upper.le U) := by
  let coeff := WilsonPositionThermometerStationNorm.cost C d
  have positive : 0 ≤ coeff := by
    dsimp [coeff,WilsonPositionThermometerStationNorm.cost]
    positivity
  filter_upwards [WilsonPositionThermometerDepositedRow.paid (f:=f) (H:=H) hc simple d 1 zero_lt_one,
    WilsonOriginalDepositedHardRate.funded simple C.path.levels 2 Q (coeff*M) ε margin]
    with k entry fee D V j grade date checked ref b size N p upper v q P column S I T _ _ J o l root old w hw small e E h he regular hard t tested
  obtain ⟨format,_,actual,physical⟩ := entry V j grade date checked ref b N p upper
  have law : q.Format (o l) C.params P := root ▸ format
  let B := (C.path.levels.params k).columns * ((C.path.levels.clock.hatBeta k) *
    (coeff*‖b‖))
  have trueBound : q.remBound (o l) P (Real.sqrt (C.path.levels.clock.forcedAllowance k)) B := by
    rw [root]
    simpa only [B,Real.rpow_one] using actual
  let β := C.path.levels.clock.hatBeta k
  have hβ : 0 ≤ β := zero_le_one.trans (C.path.levels.fits.delayed k).le
  have hc₀ : 0 ≤ (C.path.levels.params k).columns := zero_le_one.trans (C.path.levels.params k).columns_ge
  have cap : w l*B ≤ (coeff*M)*β^2 := by
    change w l*((C.path.levels.params k).columns*(β*(coeff*‖b‖))) ≤ _
    calc _ ≤ 1*(β*(β*(coeff*M))) := by gcongr
         _ = _ := by ring
  refine ⟨law,fee old.K l q law t w hw hard tested trueBound cap,?_⟩
  intro x U
  rw [WilsonOriginalDepositedDensity.original old l q law (C.localSection j) t w hw he regular hard tested trueBound]
  apply congrArg (t x * ·)
  rw [root]
  exact physical U

end YM.Integration.WilsonOriginalStarSourceIntake
