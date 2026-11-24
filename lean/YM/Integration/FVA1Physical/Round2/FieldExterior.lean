import YM.Integration.FVA1Physical.Wilson.OrbitCalibration
import YM.Integration.FVA1Physical.Wilson.HotelTest
import YM.Integration.FVA1Physical.Sources.Round2.GlobalSchurBounds

/-! Transfer a single exterior-independent reading from the good conditional
fibres to the actual unrestricted posterior. The rare-set loss is uniform
even before a magnitude bound for the proposed Wilson reading is available. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open MSbar.Bulk MSbar.Whisk MSbar.Rolling MSbar.Cacao MSbar.Mosaic RGComparison.Core16
open Push Push.Uniform SectorNext.Vacuum YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G : Gauge}

theorem exterior_field_average {c f : Side} {S : StepData c f} {R : Rep G f} (O : Config G c)
    {F : Forest S.ratio} {X Y : Support f} {A : Set (Config G f)} {r φ : Config G f → ℝ}
    {σ C δ Λ w a κ χ ε : ℝ} (hA : MeasurableSet A)
    (adm : Admitted O R S σ C δ Λ w) (rota : Rota (S:=S) R O Y F (board F X) A r a κ)
    (tact : Tonic.Loan.Tact F X A r Y R O 1 χ) (rare : chance S R O Aᶜ ≤ χ)
    (hχ : 0 ≤ χ) (small : χ ≤ 1/2) (localφ : GaugeLocal S Y φ) (bounded : ∀ U, |φ U| ≤ 1)
    (W : ℝ) (hε : 0 ≤ ε)
    (inside : ∀ U ∈ A, |Rota.resample F (board F X) r A φ U - W| ≤ ε) :
    |expect S R O φ - W| ≤ 2*ε + 10*χ := by
  let T := Rota.resample F (board F X) r A φ
  let E := expect S R O
  obtain ⟨env,near⟩ := signed_tact adm rota tact localφ bounded
  let cut := A.indicator (fun _ => W)
  have point (U) : |cut U - T U| ≤ ε := by
    by_cases hu : U ∈ A
    · rw [show cut U=W from Set.indicator_of_mem hu _,abs_sub_comm]
      exact inside U hu
    have van : T U = 0 := by
      simp only [T,Rota.resample,Rota.ghat,show spec A U=0 from Set.indicator_of_notMem hu _,zero_mul,integral_zero]
    simpa only [cut,Set.indicator_of_notMem hu,van,sub_zero,abs_zero] using hε
  have between : |E cut - E T| ≤ ε :=
    expect_difference adm (measurable_const.indicator hA) env point
  have tail := expect_on_chart O hA adm (fun _ => W) measurable_const (abs_nonneg W)
    (fun _ => le_rfl) rare
  rw [e_const O adm W] at tail
  have middle : |E T-E cut| ≤ ε := (abs_sub_comm _ _).le.trans between
  have tail' : |E cut-W| ≤ |W| * χ := (abs_sub_comm _ _).le.trans tail
  have diff : |E φ - W| ≤ ε+(4+|W|)*χ := by
    calc |E φ-W| ≤ |E φ-E T| + |E T-W| := abs_sub_le ..
         _ ≤ 4*χ + (|E T-E cut|+|E cut-W|) := add_le_add (by simpa only [abs_sub_comm] using near) (abs_sub_le ..)
         _ ≤ 4*χ + (ε + |W| * χ) := add_le_add le_rfl (add_le_add middle tail')
         _ = _ := by ring
  have eφ : |E φ| ≤ 1 := expect_unit_any O adm φ bounded
  have wbound : |W| ≤ 1 + |E φ-W| := by
    have h := abs_sub_le W (E φ) 0
    rw [sub_zero,sub_zero,abs_sub_comm W] at h
    linarith only [h,eφ]
  have absorb := mul_le_mul_of_nonneg_left small (abs_nonneg (E φ-W))
  have paid := (mul_le_mul_of_nonneg_right (add_le_add_left wbound 4) hχ)
  nlinarith only [diff,paid,absorb]

end YM.Integration.FVA1Physical.Round2.Curvature
