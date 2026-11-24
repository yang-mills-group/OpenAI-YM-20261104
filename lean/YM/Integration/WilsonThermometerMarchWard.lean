import YM.Integration.WilsonThermometerReferenceMesh
import YM.Integration.WilsonAddressedMatchedEquation
import YM.Integration.WilsonAddressedThermometerIntake

/-! The full signed, displaced equation return on each of the three actual corrected fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchWard
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open Labels Source Bid Cells Push FullVolume MergeProof Next.Extract Extra.Histories XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {T : Table R.family.book}
variable (F : Final R.family f T) (J : ℝ → tower T) (V : Store G) {H : (Bel R.family.book).Hierarchy}
    {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → Group R.family 6)
variable {E : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
  {P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d} {b : Presentation R.family}

def Delivered (E : ∀ d, SectionData (R.family.labels.level d))
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (b : Presentation R.family) : Prop :=
    ∀ᶠ r in trail, let Z:=adjusted F J V A r
      ∀ᶠ N : ℕ in atTop, ∃ h : Z.station.k ≤ N, ∀ p (s : Badge) (i : Fin 3)
        {m : ℕ} (earlier : m ≤ Z.station.k) (t : Site (R.family.side m p)) (o : Site (R.family.side N p)),
        let S:=center R.family.S p (earlier.trans h) 0
        let x : R.family.label (grade i).val := Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i)
        o ∈ S.margin t (3*span R.family.S h p) →
        ∃ Y : Config G (R.family.side N p) → ℂ, Interior (S.chamber 0) Y ∧
          S.rootTest (R.family.beta N p) Y ≤ 2*Fintype.card (R.family.labels.level (grade i)).Index *
            WilsonThermometerMarchReference.fee R.family s i * Real.exp (-(1/128:ℝ)*R.family.S.scale N) ∧
          S.copy t Y = WilsonOffsetReportingProducts.residual R.family (E (grade i)) N p (P (grade i) (N,p))
            (x-b.step (grade i) (N,p) x) o

/-- One choice of the physical hierarchy and its original gauge equation for every arm and every face. -/
theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a)) :
    Delivered F J V A E P b := by
  unfold Delivered
  have go : Tendsto (fun r=>(adjusted F J V A r).station.k) trail atTop :=
    tendsto_atTop.mpr fun m=>(paid m).mono fun _ h=>h.1
  have each (i : Fin 3) := WilsonAddressedMatchedEquation.original R (d:=(grade i).val) simple portfolio house
  filter_upwards [WilsonThermometerMarchReference.original F J V A simple paid lead (1/128) (by norm_num),
    paid 0,go.eventually (eventually_all.mpr each)] with r bounded raw matched
  dsimp only
  let Z:=adjusted F J V A r
  filter_upwards [eventually_gt_atTop Z.station.k,eventually_all.mpr matched] with N above all
  refine ⟨above.le,?_⟩
  intro p s i m earlier t o inside
  let x : R.family.label (grade i).val := Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i)
  obtain ⟨h,offered⟩ := all i
  obtain ⟨Y,localY,price,field⟩ := offered p x earlier t o inside
  have norm : ‖x‖ ≤ (R.family.labels.level (grade i)).coeffSize x :=
    (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg _ _)).mpr fun j=>
      Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ j)
  have anchor := norm.trans (bounded N p above s i)
  have clock := WilsonThermometerReferenceMesh.cutoff Z.station raw.2.1 above.le
  have radius : Z.station.wheel.r = r := raw.2.2.1
  rw [radius] at clock
  have vanish : Real.exp ((1/128:ℝ)*(-Real.log r)) * Real.exp (-(1/64:ℝ)*R.family.S.scale N)
       ≤ Real.exp (-(1/128:ℝ)*R.family.S.scale N) := by
    rw [←Real.exp_add,Real.exp_le_exp]
    linarith only [clock]
  let fee:=WilsonThermometerMarchReference.fee R.family s i
  have fee0 : 0≤fee := by
    have sign := anchor.trans' (norm_nonneg _)
    exact nonneg_of_mul_nonneg_right sign (Real.exp_pos _)
  refine ⟨Y,localY,price.trans ?_,field⟩
  calc
    _ ≤ (2*(Fintype.card (R.family.labels.level (grade i)).Index:ℝ)) *
        (Real.exp ((1/128:ℝ)*(-Real.log r))*fee) * Real.exp (-(1/64:ℝ)*R.family.S.scale N) := by
          gcongr
    _ = (2*(Fintype.card (R.family.labels.level (grade i)).Index:ℝ))*fee *
        (Real.exp ((1/128:ℝ)*(-Real.log r))*Real.exp (-(1/64:ℝ)*R.family.S.scale N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left vanish (by positivity)

theorem appointed (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J) :
    ∃ (E : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G), ∃ P b,
    (∀ d, Mark.Portfolio R.family.params (E d) (W d)) ∧
      Hearthside R.family E W P b (Bandage.fly R.alloy.B.a) ∧
      WilsonAddressedEquationMoments.Placed R E P b ∧ Delivered F J V A E P b := by
  obtain ⟨E,W,P,b,portfolio,house,placed,_⟩ := WilsonAddressedThermometerIntake.original R simple
  exact ⟨E,W,P,b,portfolio,house,placed,original F J V A simple paid lead portfolio house⟩

end YM.Integration.WilsonThermometerMarchWard
