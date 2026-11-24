import YM.Integration.WilsonIndependentNotebookDoseReturn

/-! The signed change of the full public Wick coordinates on the same held clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonIndependentNotebookDoseCoefficients
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open Filter Function Finset Matrix Lattice RG Laurent Bloch Wilson Tree Power PowerSeries
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider Precision Exterior Gauge Source Labels WardBin Bulb Realm
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Classical
variable {G:Gauge}{k u e:ℕ}

def sample (B:Cost)(q:ℕ)(t:ℝ):Cost→ₗ[ℝ]ℂ:=
  Complex.ofRealCLM.toLinearMap.comp
    ((∑j∈range (q+1),t^j • PowerSeries.coeff (R:=ℝ) j).comp
    (substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (by simp:constantCoeff (B*PowerSeries.X)=0))).toLinearMap)

theorem actual (A:Levels G)(O:ChartRatio G)(N m host q:ℕ)(h:host ≤ m)(t:ℝ)(v:Cost):
    cash q t (embed (clock A O N m host v))=sample (relativeF A O N host (m-host)) q t v:=by
  have phase:=WilsonIndependentFittedRelativeClock.reported A O N host (m-host) v
  rw [show host+(m-host)=m by omega] at phase
  rw [phase]
  let B:=relativeF A O N host (m-host)
  change (∑j∈range (q+1),(t:ℂ)^j*coeff j (embed (reel B v)))=
    (↑((∑j∈range (q+1),t^j • PowerSeries.coeff (R:=ℝ) j) (reel B v)):ℂ)
  simp [embed,PowerSeries.coeff_map,Complex.ofReal_pow,Complex.ofReal_mul]

/-- Both signed matrix directions hold before summation against any observer. -/
theorem coefficients (H:Hol G)(Q:SealR G)(w:Rails Q.h k u e)(E W B V:Credit)
    (X:CutsP H Q.ans Q.path w E W B V)(a:ℝ)(host q:ℕ)(h:host ≤ X.m)(t:ℝ):
    let seen:=fun c=>cash q t (embed (clock X.ax X.tx X.N X.m host c))
    let M:=Wray X.ax X.tx Q.ans Q.path X.N X.m
    (∀i,seen (dose X a i)=∑j,(M⁻¹ i j) • seen (publicDose Q X a j)) ∧
    (∀i,seen (publicDose Q X a i)=∑j,(M i j) • seen (dose X a j)):=by
  intro seen M
  let read:=sample (relativeF X.ax X.tx X.N host (X.m-host)) q t
  have paid(c):seen c=read c:=actual _ _ _ _ _ _ h _ c
  simp only [paid]
  constructor
  · intro i
    nth_rw 1 [←(WilsonPositionProgramTrialHomeDose.original Q X a).1]
    exact (map_sum read _ _).trans (Finset.sum_congr rfl (fun _ _=>map_smul read _ _))
  · intro i
    exact (map_sum read _ _).trans (Finset.sum_congr rfl (fun _ _=>map_smul read _ _))

end YM.Integration.WilsonIndependentNotebookDoseCoefficients
