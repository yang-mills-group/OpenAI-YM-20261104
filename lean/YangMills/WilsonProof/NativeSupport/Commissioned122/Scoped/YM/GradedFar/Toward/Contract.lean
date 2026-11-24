import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Formal
import YM.FVA2.O.Canon.Give
/-!
# Use Match conversion on the exact prediction coefficients

As in the final graded far-field interface -- THIS MS_Data, not an arbitrary
MS graph identification. For c choose the same alphabets, apply seats of precisely Z
and its inverse (grade-preserving) on outputs after inserting f(t),Z(t) on
all input OPE slots. Here define that substitution with the stock `refund`
(`Project/Vault`, from `Gift`) then crop. No analytic assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set O O.Score O.Enh O.Read O.Canon PowerSeries
open XSpace XSpace.Normalize Scale Register MS.Land Dframe O.Project
open scoped Topology Classical BigOperators
variable {G : Gauge} {n h H p : ℕ} {d : Fin n → ℕ}
    (N : WilsonPrescription G) (ν : ℝ) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {Sms : MS.Land.Prescription (Press.portDeck G)} {hG : G.Simple}
local notation "V♪" => Scale.Measure.outlook N.scheme N.criterion
local notation "Y♪" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "Z" => Measure.Z N.scheme N.criterion ν M
local notation "wave" => Equator.wave ν M
local notation "f" => Measure.f N.criterion ν M

def MStariff (x : Points n) (u : Appointed122Fields G d) (q : Q G) : PowerSeries ℂ :=
  ∑ i : Words G d, PowerSeries.C (filedMultipliers122 u i) *
    refund (seats Z) (seats (replay Z)) f (fun t : Scan G n => OPECoefficients wave t 0 x) (labeling i) q

def MScoefficient (x : Points n) (h p : ℕ) (g : ℂ) (u : Appointed122Fields G d) : Sec G h :=
  ∑ i : Toon G h, filedCrop122 p g (MStariff N ν M x u (flash i)) • theory i

theorem exact_MS_tariff (he : Main.Match N hG M Sms true) (x : Points n) (u : Appointed122Fields G d) (q : Q G) :
    MStariff N ν M x u q = tariff V♪ x u q := by
  have hv : Civil Z := ⟨fun h => (he.frame ν h).1, fun h => (he.frame ν h).2, fun hs => he.frameCompat ν _ _ hs⟩
  have hp (v : Scan G n) := (he.separatedOPE ν).wilson.start_u v
  refine Finset.sum_congr rfl fun i _ => ?_
  apply congr_arg
  let L := fun t : Scan G n => OPECoefficients wave t 0 x
  let c := OPECoefficients V♪ (labeling i) 0 x
  have h : credit (seats Z) f L (labeling i)=receipt (seats Z) c := (he.separatedOPE ν).gifts (labeling i) 0 x
  change receipt (seats (replay Z)) (credit (seats Z) f L (labeling i)) _= _; rw [h,timely,spin_v hv,receipt_K]; unfold c; rw [hp]

lemma exact_MS (he : Main.Match N hG M Sms true) (x : Points n) (u : Appointed122Fields G d) (h p : ℕ) (g : ℂ) :
    MScoefficient N ν M x h p g u = filedVector122 V♪ x h p g u := by simp_rw [MScoefficient, filedVector122, exact_MS_tariff N ν M he]

-- same substitutions in correlators. correlation theorem uses conf proof; expose coefficients.
-- can directly specialize stock `PositionHomogeneousComparison.filed` also.
def MScorrelation (x : Scale.Stage n) (hd : Covered d H) (p : ℕ) (g : ℂ) (u : Appointed122Fields G d) : ℂ :=
  ∑ i∈Finset.range (p+1), g^i *
    Facets.actMark (Z H) (Facets.couple f (wave H)) n x i (fun j=> up (hd j) (u j))
end YM.FVA2.GradedFar
