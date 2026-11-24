import YM.Integration.WilsonOrdinaryRelativeSource

/-! Actual numerical same-height price between two independently filed
prescription times. The spectator remains inside every signed prior Gibbs
integral; the original marginal engineering powers are not discarded. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryRelativeTariff
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryHomogeneousDetectors

open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 Extra.Histories
open RegulatorIR.FVAAlt2.Lodge WilsonFactoryFiledGlyphs WilsonOrdinaryUltravioletPair
open WilsonOrdinaryPositionDecoder WilsonOrdinaryHomogeneousDetectors
variable {F : Final R.family f S} (L : Layout F) (d : ℕ)
variable {B : Deck G}

open MS.Land MS.Rake MS.Book MS.Book.Program
open FVAAlt2.Lobby FVAAlt2.Billing PowerSeries
open MeasureTheory
open WilsonPhysicalExteriorFeeShift WilsonPhysicalExteriorRunningRows
open WilsonPhysicalExteriorMeasuredTariff
open WilsonOrdinaryPricedGlyph
open Precision
open WilsonOrdinaryRelativeSource MeasureTheory
variable (R) {W : Type} {O : Booked B} (Q : MS.Land.Prescription B)
variable (a b : ℝ) (h : ℕ) (z : UVIndex) (u : ℝ) (x : Site (R.family.side z.1 z.2))
set_option quotPrecheck false
local notation "Conf!" => Config G (R.family.side z.1 z.2)
local notation "μ!" => Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)

def old (ε : ℝ) (s : Glyph B h) (k : ℕ) (U : Conf!) : ℂ :=
  ((ε:ℂ)^s.size)⁻¹ * PowerSeries.coeff k (WilsonOrdinaryRelativeSource.previous R Q a b h z u x U s)

def heard (ε : ℝ) (s : Glyph B h) (k : ℕ) (H : Conf!→ℂ) : ℂ :=
  Wilson.moment (R.family.beta z.1 z.2) (fun U=>old R Q a b h z u x ε s k U * H U)

theorem continuous_old (coupled : u≠0) (ε : ℝ) (s : Glyph B h) (k : ℕ) :
    Continuous (old R Q a b h z u x ε s k) := by
  have live (v : Glyph B h) : Continuous (material R (owner v) z.1 z.2 u x) := by
    let c := (R.family.S.a z.1:ℂ)^(owner v).h
    have hc : c≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')
    have same : material R (owner v) z.1 z.2 u x = fun U=>c*R.family.O z.1 z.2 (ledger R (owner v) z.1 z.2 u) x U := by
      funext U
      rw [WilsonFactoryFiledGlyphs.visible R (owner v) z.1 z.2 u coupled]
      change _ = c*(c⁻¹ * _)
      rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
    rw [same]
    exact continuous_const.mul (R.family.continuousO _ _ _ _ _)
  unfold old
  simp only [WilsonOrdinaryRelativeSource.previous,map_sum,PowerSeries.coeff_mul_C]
  exact continuous_const.mul (continuous_finsetSum _ fun v _=>continuous_const.mul (live v))

private theorem integrate {α I K : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : Finset I) (B : Finset K) (c : I→K→ℂ) (X : I→K→α→ℂ)
    (paid : ∀ i j,Integrable (X i j) μ) :
    (∫ U,∑ i∈A,∑j∈B,c i j*X i j U ∂μ) = ∑i∈A,∑j∈B,c i j*(∫ U,X i j U ∂μ) := by
  classical
  rw [integral_finsetSum _ fun i _=>integrable_finsetSum _ fun j _=>(paid i j).const_mul _]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _=>(paid i j).const_mul _]
  simp only [integral_const_mul]

private theorem price {I K : Type*} (A : Finset I) (B : Finset K) (c x : I→K→ℂ)
    (M : ℝ) (cap : ∀ i∈A,∀j∈B,‖c i j‖≤M) :
    ‖∑ i∈A,∑j∈B,c i j*x i j‖ ≤ M*∑i∈A,∑j∈B,‖x i j‖ := by
  calc
    _ ≤ ∑i∈A,‖∑j∈B,c i j*x i j‖ := norm_sum_le ..
    _ ≤ ∑i∈A,∑j∈B,M*‖x i j‖ := Finset.sum_le_sum fun i hi=>
      (norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (cap i hi j hj) (norm_nonneg _))
    _ = _ := by simp only [Finset.mul_sum]

/-- Exact signed two-clock measurement, with the full true spectator in
each earlier normalized integral. -/
theorem signed (M : MS_Data G O) (hG : G.Simple)
    (paid : TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (p : W→MS.Rake.Label B) (i : W) (k : ℕ) (ε : ℝ) (admit : ε≠0) (coupled : u≠0)
    (Y : Conf!→ℂ) (Yc : Continuous Y) :
    Wilson.moment (R.family.beta z.1 z.2) (fun U=>WilsonOrdinaryPricedGlyph.field R Q b p ε i k z u x U * Y U)=
      ∑s ∈ Finset.univ.filter (fun s : Glyph B (p i).h=>s.size=(p i).h),
      ∑j ∈ Finset.HasAntidiagonal.antidiagonal k, PowerSeries.coeff j.1 (coordinates Q (p i).h b a b (Land.read (p i).item) s) *
        heard R Q a b (p i).h z u x ε s j.2 Y := by
  classical
  let H := (p i).h
  let V := Finset.univ.filter (fun s : Glyph B H=>s.size=H)
  let T := Finset.HasAntidiagonal.antidiagonal k
  let c (s : Glyph B H) (j : ℕ×ℕ) := PowerSeries.coeff j.1 (coordinates Q H b a b (Land.read (p i).item) s)
  let A (s : Glyph B H) (j : ℕ×ℕ) := fun U=>old R Q a b H z u x ε s j.2 U*Y U
  have finance s j : Integrable (A s j) μ! := Wilson.continuous_integrable _
    ((continuous_old R Q a b H z u x coupled ε s j.2).mul Yc)
  change (∫ U,WilsonOrdinaryPricedGlyph.field R Q b p ε i k z u x U*Y U ∂μ!) =
    ∑s∈V,∑j∈T,c s j*(∫ U,A s j U ∂μ!)
  rw [←integrate μ! V T c A finance]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [convolution R Q a b z u x U M hG paid p i k ε admit coupled]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j _
  have height : s.size=H := (Finset.mem_filter.mp hs).2
  change (((ε:ℂ)^H)⁻¹ * (c s j * PowerSeries.coeff j.2 (WilsonOrdinaryRelativeSource.previous R Q a b H z u x U s)))*Y U=
    c s j*(((ε:ℂ)^s.size)⁻¹*PowerSeries.coeff j.2 (WilsonOrdinaryRelativeSource.previous R Q a b H z u x U s)*Y U)
  rw [height]; ring

/-- One authentic finite-log cost before every admissible time, actual stage,
regulator, filed source, spectator and perturbative degree up to the
requested horizon. No unsigned norm is put inside the prior Wilson read. -/
theorem original (M : MS_Data G O) (hG : G.Simple)
    (paid : TaylorOKPl M (Lobby.Table (basisR R) B) Q) (D m : ℕ) :
    ∃ A : ℝ,0≤A ∧ ∃ e : ℕ,∀ (a b : ℝ) (z : UVIndex) (u : ℝ) (x : Site (R.family.side z.1 z.2))
      (p : W→MS.Rake.Label B) (i : W), (p i).h≤D → ∀ k ≤ m,∀ ε : ℝ,ε≠0 → u≠0 →
      ∀ Y : Config G (R.family.side z.1 z.2)→ℂ,Continuous Y →
        ‖Wilson.moment (R.family.beta z.1 z.2) (fun U=>WilsonOrdinaryPricedGlyph.field R Q b p ε i k z u x U*Y U)‖ ≤
        (A*(WilsonPhysicalExteriorMeasuredTariff.length ![b,a,b])^e) *
        ∑s∈Finset.univ.filter (fun s : Glyph B (p i).h=>s.size=(p i).h),
        ∑j∈Finset.HasAntidiagonal.antidiagonal k,‖heard R Q a b (p i).h z u x ε s j.2 Y‖ := by
  classical
  obtain ⟨A,hA,e,quoted⟩ := WilsonPhysicalExteriorMeasuredTariff.paid Q D m
  refine ⟨A,hA,e,?_⟩
  intro a b z u x p i hi k hk ε hε hu Y continuousY
  rw [signed R Q a b z u x M hG paid p i k ε hε hu Y continuousY]
  apply price
  intro s _ j hj
  have move : j.1+j.2=k := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
  exact quoted (p i).h hi j.1 (by omega) (Land.read (p i).item) s ![b,a,b]

end YM.Integration.WilsonOrdinaryRelativeTariff
