import YM.Integration.WilsonIndependentFittedPivotRoster
import YM.Integration.WilsonIndependentFittedPivotCash
import YM.Integration.WilsonIndependentMatchedCensusReceipt

/-! The actual finite roster of fitted coefficients is evaluated in the same
reported kinetic chart as the signed mixed row. All lower pivots are present. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankCash
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentFittedMixedCash (bill embed)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentFittedPivotCash (measured view gross)

def amount (X:CutsP H T p v E W K U)(s q:ℕ)(g:ℝ)(d:Verse F):ℝ:=
  ∑j,‖cash q g (embed (clock X.ax X.tx X.N X.m s (d j)))‖

def reserve (X:CutsP H T p v E W K U)(s q:ℕ)(d:Verse F):ℝ:=
  ∑j,WilsonPhysicalMarkedDefect.RawProduct.belt q (embed (clock X.ax X.tx X.N X.m s (d j)))

theorem separated (X:CutsP H T p v E W K U)(s q:ℕ)(g:ℝ)(d:Verse F):
    gross X s q g d=amount X s q g d+2*|g|^(q+1)*reserve X s q d:=by
  unfold gross amount reserve bill
  rw [sum_add_distrib,mul_sum]

theorem original (X:CutsP H T p v E W K U)(s:ℕ)(older:s≤X.m)(P:Era G ℝ)(prior:Auth k P)
    (d:Verse F)(ψ:Rarity D)(y:ℝ)(o:CellR)(q:ℕ)(cap:q≤e)(t:ℝ)(small:|t|≤1)
    (x:Fin 0→YForest G)(u:ℕ)(A B:ℝ):
    let U:=fun j=>film X j 0 ψ y o X.i
    let M:=planted X d ψ y o
    ((∀j,Hearing X P (U j) s u A) →
      ‖view X s q t P M x‖≤gross X s q t d*(((q+1:ℕ):ℝ)*A)) ∧
    ((∀j,Hearing X (U j) P s u B) →
      ‖view X s q t M P x‖≤gross X s q t d*(((q+1:ℕ):ℝ)*B)):=by
  intro U M
  obtain ⟨out,back⟩:=WilsonIndependentFittedPivotRoster.joined X P prior s older d ψ y o 0 x
  have pay (j:Alma F)(S Z:Era G ℝ)(fee:ℝ)(paid:Hearing X S Z s u fee):
      ‖measured q t (clock X.ax X.tx X.N X.m s (d j)*word X s S Z 0 x)‖≤
        bill q t (clock X.ax X.tx X.N X.m s (d j))*(((q+1:ℕ):ℝ)*fee):=by
    have pos:0≤bill q t (clock X.ax X.tx X.N X.m s (d j)):=by
      unfold bill
      exact add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))
        (WilsonPhysicalMarkedDefect.RawProduct.positive q _))
    exact (WilsonIndependentFittedMixedCash.product q t small _ _).trans
      (mul_le_mul_of_nonneg_left (WilsonIndependentFittedMixedCash.stopped X S Z s q u cap fee paid x) pos)
  constructor
  · intro registered
    unfold view
    rw [show word X s P M 0 x=_ from out,map_sum,gross,sum_mul]
    exact (norm_sum_le _ _).trans (sum_le_sum fun j _=>pay j P (U j) A (registered j))
  · intro registered
    unfold view
    rw [show word X s M P 0 x=_ from back,map_sum,gross,sum_mul]
    exact (norm_sum_le _ _).trans (sum_le_sum fun j _=>pay j (U j) P B (registered j))

end YM.Integration.WilsonIndependentConditionedBankCash
