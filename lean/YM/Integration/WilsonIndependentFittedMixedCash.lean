import YM.Integration.WilsonIndependentFittedMixedReturn
import YM.Integration.WilsonIndependentFittedNumericalProduct
import YM.Integration.WilsonIndependentMatchedPivotStop

/-! At a signed older hearing the complete numerical fitted dose is charged
once. Only the finite convolution remainder sees its full coefficient sum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedMixedCash
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (axis film)
open WilsonIndependentFittedReportedFilm (weight)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical

def embed:Cost→+*PowerSeries ℂ:=PowerSeries.map (algebraMap ℝ ℂ)
def bill (Q:ℕ)(t:ℝ)(C:Cost):ℝ:=‖cash Q t (embed C)‖+2*|t|^(Q+1)*belt Q (embed C)

theorem cash_le (Q:ℕ)(t:ℝ)(small:|t|≤1)(A:PowerSeries ℂ):
    ‖cash Q t A‖≤belt Q A:=by
  unfold WilsonPhysicalMarkedDefect.RawBank.cash WilsonPhysicalMarkedDefect.RawProduct.belt
  apply (norm_sum_le _ _).trans
  refine sum_le_sum fun j _=>?_
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg t) small)

theorem product (Q:ℕ)(t:ℝ)(small:|t|≤1)(C A:Cost):
    ‖cash Q t (embed (C*A))‖≤bill Q t C*belt Q (embed A):=by
  rw [map_mul]
  let u:=embed C;let v:=embed A
  have gap:=WilsonIndependentFittedNumericalProduct.signed Q small univ (![u,v]:Fin 2→PowerSeries ℂ)
  have one:‖cash Q t (u*v)-cash Q t u*cash Q t v‖≤2*|t|^(Q+1)*(belt Q u*belt Q v):=by
    rw [norm_sub_rev];simpa [Fin.prod_univ_two] using gap
  have fees:=mul_le_mul_of_nonneg_left (cash_le Q t small v) (norm_nonneg (cash Q t u))
  calc
    ‖cash Q t (u*v)‖≤‖cash Q t (u*v)-cash Q t u*cash Q t v‖+‖cash Q t u*cash Q t v‖:=
      (norm_le_insert' _ _).trans_eq (add_comm _ _)
    _≤2*|t|^(Q+1)*(belt Q u*belt Q v)+‖cash Q t u‖*belt Q v:=
      add_le_add one (by rwa [norm_mul])
    _=bill Q t C*belt Q v:=by unfold bill;dsimp [u,v];ring

variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}
theorem stopped (X:CutsP H T p v E W K U)(P Q:Era G ℝ)(s q u':ℕ)(budget:q≤e)(fee:ℝ)
    (sale:Hearing X P Q s u' fee)(x:Fin 0→YForest G):
    belt q (embed (word X s P Q 0 x))≤((q+1:ℕ):ℝ)*fee:=by
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt
  calc
    _≤∑_j∈range (q+1),fee:=by
      refine sum_le_sum fun j hj=>?_
      have paid:=sale.2 j ((Nat.lt_succ_iff.mp (mem_range.mp hj)).trans budget) x
      simpa [embed,word,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_map] using paid
    _=_:=by simp

theorem original (X:CutsP H T p v E W K U)(s:ℕ)(older:s≤X.m)(a:ℝ)(c:Cost)
    (j:Alma F)(l:ℕ)(φ ψ:Rarity D)(y:ℝ)(o:CellR)(q:ℕ)(cap:q≤e)(t:ℝ)(small:|t|≤1)
    (x:Fin 0→YForest G)(u':ℕ)(A B:ℝ):
    let P:=seat X a φ y o X.i
    let F₀:=film X j l ψ y o X.i
    let M:=planted X (weight c (axis j l)) ψ y o
    let C:=clock X.ax X.tx X.N X.m s c
    Hearing X P F₀ s u' A → Hearing X F₀ P s u' B →
      ‖cash q t (embed (word X s P M 0 x))‖≤bill q t C*(((q+1:ℕ):ℝ)*A) ∧
      ‖cash q t (embed (word X s M P 0 x))‖≤bill q t C*(((q+1:ℕ):ℝ)*B):=by
  intro P F₀ M C left right
  obtain ⟨out,back⟩:=WilsonIndependentFittedMixedReturn.original X s older a c j l φ ψ y o 0 x
  have balance:0≤bill q t C:=
    add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (abs_nonneg _) _))
      (WilsonPhysicalMarkedDefect.RawProduct.positive q _))
  constructor
  · rw [show word X s P M 0 x=_ from out]
    exact (product q t small C _).trans (mul_le_mul_of_nonneg_left (stopped X P F₀ s q u' cap A left x) balance)
  · rw [show word X s M P 0 x=_ from back]
    exact (product q t small C _).trans (mul_le_mul_of_nonneg_left (stopped X F₀ P s q u' cap B right x) balance)

end YM.Integration.WilsonIndependentFittedMixedCash
