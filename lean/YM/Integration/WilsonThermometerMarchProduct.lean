import YM.Integration.WilsonThermometerMarchWard
import YM.Integration.WilsonThermometerReflectedChange
import YM.Integration.WilsonThermometerReflectedColumns
import YM.Integration.WilsonThermometerReverseWard

/-! The three actual displaced thermometer fields and the complete projected
physical product on one original Wilson ensemble, at every paid real radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerMarchProduct
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open RG Labels Source Push Cells Lattice Wilson MergeProof XSpace XSpace.Rose
open RG17 PhysMS PhysMS.Frame Maxwell XSpace.Normalize Bid FullVolume Next.Extract Extra.Histories
open Next.Rank.Tapes.West Next.Rank.East MergeProof.East Dash PhysicalNext.RankCovariance Further.CorrectedLift
open Next.Rank Next.Rank.Tapes Next.Rank.Station Next.Rank.Price
open PhysicalNext.Repeat Legato Bandage
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap WilsonAddressedEquationShelf
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {T : Table R.family.book}
variable (F : Final R.family f T) (J : ℝ → tower T) (V : Store G)
    {H : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → Group R.family 6)
local notation "L" => R.family.path.levels

def field (Z : Group R.family 6) (N p : ℕ) (s : Badge) (i : Fin 3) : R.family.label (grade i).val :=
  Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i)

def price (Q : Fin 3 → ℝ) (Z : Group R.family 6) (s : Badge) : ℝ :=
  (1+∑ i : Fin 3, |2*(Fintype.card (R.family.labels.level (grade i)).Index : ℝ)*
      WilsonThermometerMarchReference.fee R.family s i|) +
    ∑ i : Fin 3, |Q i * R.family.path.levels.clock.hatBeta Z.station.k *
      (WilsonPositionThermometerStationNorm.cost R.family (grade i)*‖vector Z s i‖)|

theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (panels : WilsonReportingAbsoluteInletLiveRun.PanelDates R)
    (E : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (b : Presentation R.family)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a)) :
    ∃ radius : ℕ → ℕ, ∃ (panel : Fin 3 → Tapes.Panel 6) (κ : ℝ),
      Checks (panel 0).arc (panel 1).arc (panel 2).arc κ (trays 6) 6 ∧
      ∀ pick : Fin 3, ∃ Q : Fin 3 → ℝ, ∀ᶠ r in trail,
        let Z:=adjusted F J V A r
        ∀ᶠ N : ℕ in atTop, ∃ h : Z.station.k ≤ N, ∀ p (s : Badge) (m : ℕ)
          (small : m ≤ widthSky L (panel pick).arc Z.station.k)
          (v : Fin 3 → Site (R.family.side m p)) (o : Fin 3 → Site (R.family.side N p)),
          let pre:=(widerSky L (panel pick).arc Z.station.k).trans (beforeSky L (panel pick).arc Z.station.k)
          let S:=center R.family.S p ((small.trans pre).trans h) 0
          Function.Injective v → WilsonOffsetReportingProducts.Avoids (C:=R.family) E radius (fun i=> (grade i).val) o →
          (∀ i, o i ∈ S.margin (v i) (3*span R.family.S (pre.trans h) p)) →
          (∀ i, o i ∈ S.margin (v i) (3*span R.family.S h p)) →
          ‖moment (R.family.beta N p) (fun U=>∏ i,
              R.family.O N p (b.step (grade i) (N,p) (field Z N p s i)) (o i) U) -
            moment (R.family.beta N p) (fun U=>∏ i,R.family.O N p (field Z N p s i) (o i) U)‖ ≤
            7*(Real.exp (-(1/128:ℝ)*R.family.S.scale N)*(price Q Z s)^3) := by
  obtain ⟨radius,erase⟩ := WilsonThermometerReverseWard.projected R E W P b portfolio house
  obtain ⟨panel,κ,geometry,available⟩ := WilsonThermometerReflectedColumns.original R simple panels f H 6
    grade 1 (by norm_num)
  refine ⟨radius,panel,κ,geometry,fun pick=>?_⟩
  obtain ⟨Q,_,cells⟩ := available pick
  have go : Tendsto (fun r=>(adjusted F J V A r).station.k) trail atTop :=
    tendsto_atTop.mpr fun m=>(paid m).mono fun _ h=>h.1
  refine ⟨Q,?_⟩
  filter_upwards [go.eventually cells, WilsonThermometerMarchWard.original F J V A simple paid lead portfolio house,
    paid 0] with r slots defect filed
  dsimp only
  let Z:=adjusted F J V A r
  filter_upwards [slots,defect,erase (Fin 3) (fun i=>(grade i).val),
    R.family.S.divergent.eventually_ge_atTop 0] with N priced changed full clock
  obtain ⟨later,roots⟩ := priced
  obtain ⟨_,remainder⟩ := changed
  refine ⟨later.le,?_⟩
  intro p s m small v o separate avoids reflected shield
  let pre := (widerSky L (panel pick).arc Z.station.k).trans (beforeSky L (panel pick).arc Z.station.k)
  let S := center R.family.S p ((small.trans pre).trans later.le) 0
  choose X loc raw registered using fun i : Fin 3 =>
    roots p m small v o Z.station (fun i=>index Z (grade i)) (vector Z s)
      (fun _=>rfl) rfl filed.2.1 reflected i
  have terms (i:Fin 3) := remainder p s i (small.trans pre) (v i) (o i) (shield i)
  choose D legal debt exactD using terms
  have whole := full p (field Z N p s) o (fun _=>1) avoids (fun _ _ _ _=>rfl)
    (Mark.cont_envelope continuous_const)
  simp only [mul_one] at whole
  rw [whole]
  let B (i : Fin 3) := 2*(Fintype.card (R.family.labels.level (grade i)).Index : ℝ)*
    WilsonThermometerMarchReference.fee R.family s i
  let A₀ (i : Fin 3) := Q i*R.family.path.levels.clock.hatBeta Z.station.k*
    (WilsonPositionThermometerStationNorm.cost R.family (grade i)*‖vector Z s i‖)
  have pos : 0≤price Q Z s := by unfold price; positivity
  have capP (i) : A₀ i ≤ price Q Z s := by
    have one := Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>|A₀ j|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
    change A₀ i ≤ (1+∑ j,|B j|)+∑ j,|A₀ j|
    linarith [le_abs_self (A₀ i),Finset.sum_nonneg (s:=Finset.univ) (f:=fun j=>|B j|) (fun j _=>abs_nonneg _)]
  have capD (i) : B i ≤ price Q Z s := by
    have one := Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>|B j|) (fun j _=>abs_nonneg _) (Finset.mem_univ i)
    change B i ≤ (1+∑ j,|B j|)+∑ j,|A₀ j|
    linarith [le_abs_self (B i),Finset.sum_nonneg (s:=Finset.univ) (f:=fun j=>|A₀ j|) (fun j _=>abs_nonneg _)]
  have hearing := WilsonThermometerReflectedChange.original S v X D (R.family.beta N p) (seamless R.makes N p)
    separate loc legal pos (Real.exp_le_one_iff.mpr (by nlinarith : -(1/128:ℝ)*R.family.S.scale N≤0))
    (fun i=>(show S.rootTest (R.family.beta N p) (X i) ≤ A₀ i from by have q₀ := raw i; rw [Real.rpow_one] at q₀; exact q₀).trans (capP i))
    (fun i=>(debt i).trans (by rw [mul_comm (Real.exp _)]; exact mul_le_mul_of_nonneg_right (capD i) (Real.exp_pos _).le))
  have fixed (i : Fin 3) : S.copy (v i) (X i) = R.family.O N p (d:=(grade i).val) (field Z N p s i) (o i) := registered i
  have returned (i : Fin 3) : S.copy (v i) (D i) = WilsonOffsetReportingProducts.residual R.family (E (grade i)) N p (P (grade i) (N,p)) (field Z N p s i-b.step (grade i) (N,p) (field Z N p s i)) (o i) := exactD i
  simp only [fixed,returned] at hearing
  exact hearing
end YM.Integration.WilsonThermometerMarchProduct
