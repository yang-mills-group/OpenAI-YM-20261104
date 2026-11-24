import YM.Integration.WilsonMarkedAngularResponse

/-! The presold normalized graph on the given Wilson flow, with the genuine
filed change of coupling and its signed primitive correction inside the
complete preimage cubature. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRunMarkedKineticComparison
open Function Filter Finset Lattice RG Precision Next.Free Wilson Exterior
open FormalBulk08
open Reef Flat Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Comparison.RG02 Adjacent PowerSeries
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm WilsonMarkedScalarEquation
open WilsonMarkedScalarResponse
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {d D : ℕ}
    (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (a : hue G)

private abbrev branches (i : ℕ) := (R.family.path.levels.blocks i 0).branches
private abbrev source (N i : ℕ) :=
  Dove.model R.family.path.levels L (branches R) R.metals.O a N i

def kinetic (N i : ℕ) : Pence :=
  Roof.epoch a (destination R.family.path.levels N i) (L i)
    R.family.path.levels.clock.kernel (source R L a N (i+1)) R.metals.O (branches R i)

/-- Freshness and evenness of the independent primitive are purchased on the
same actual run at each legal observation. -/
theorem base (simple : G.Simple) {N i : ℕ} (hi : i<N) :
    Wine.Fresh (kinetic R L a N i) ∧ Wine.Still (kinetic R L a N i) := by
  let h := (Dove.genu R.family.path.levels L (branches R) R.metals.O a R.alloy.B.ratio simple
    (i:=i+1) (N:=N) hi).toStory
  have story := Bank.creed (destination R.family.path.levels N i) (L i)
    (source R L a N (i+1)) R.metals.O (branches R i) h (R.family.path.levels.clock.adm i) R.alloy.B.ratio
  exact Wine.sig_mat a _ story R.family.path.levels.clock.kernel.penalty_pos (R.family.path.levels.clock.adm i)

/-- Actual signed rank charge; all the primitive inputs are independently
named before asking for a test ray, a wrapped address or an angular rank. -/
def correction (c : Caliber) (cap : ℕ) (H : Pence) (e j r : ℕ) : ℂ :=
  let A := rate (c.back cap)
  let U := reciprocal (c.back cap)
  let B := PowerSeries.map Complex.ofRealHom (Wine.bookH H)
  let V := PowerSeries.map Complex.ofRealHom (Wine.bookU H)
  let b := fun k => ((coeff k H : ℝ) : ℂ)
  coeff (e-j) ((table cap (fun k => (c.measure k : ℂ) - b k) A * resolver cap b A B) *
    (difference A B j * U^r - B^j*(U*V)*difference U V r))

variable (depth : d < D) (simple : G.Simple) (origin : Loc G 1)
    (c : Caliber) (cap N i per : ℕ) (hi : i<N)
    (trained : d ≤ R.family.path.levels.clock.J (i+1))
    (tags : (n : Side) → (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel n).Choices)
    (b : Letter (R.family.labels.level d)) (f : Dawn.Studio D) (e r : ℕ) (he : e ≤ cap)
    (v : chain (wire G (R.family.S.side i per)) r)

include simple origin hi trained he

/-- The actual reverse-chart weights, minus their explicitly calculated
vacuum liability, give the prebooked normalized output after summing all
offsets, wrapping each independent field direction, and taking the genuine
auxiliary torus limit. No equality of the two vacuum readings is assumed. -/
theorem compensated :
    let n := R.family.S.side i per
    let P := destination R.family.path.levels N i
    let W := source R L a N (i+1)
    let y := WilsonRunFormalMarkedStep.graph R L a depth N (i+1)
    let H := kinetic R L a N i
    Tendsto (fun m : Side => ∑ k ∈ range (e+1),
      (physicalWeight c cap e k r - correction c cap H e k r).re *
      Shore.cores (Shore.tray m n)
        (rancho (WilsonFormalMarkedCubature.finiteTransfer P (L i) W R.metals.O (branches R i)
         (Elm.growL R.family.path.levels i) (y b) d (slots (R.family.labels.level d) b)
         f (m*n) (tags (m*n))) k r) v)
      atTop (𝓝 (rancho (Kemp.banner d ((Roof.larch (WilsonRunFormalMarkedStep.graph R L a depth N i)
        (WilsonRunFormalMarkedStep.matrix R L a depth N i)) b f) n) e r v)) := by
  intro n P W y H
  have old := WilsonRunFormalMarkedStep.measured R L a depth simple origin N i per hi trained tags b f e r v
  refine old.congr' (Filter.Eventually.of_forall fun m => ?_)
  apply Finset.sum_congr rfl
  intro k hk
  have k₀ : k ≤ e := Nat.le_of_lt_succ (mem_range.mp hk)
  have price := WilsonMarkedAngularResponse.weight c cap H (base R L a simple hi).1 k₀ he r
  change physicalWeight c cap e k r - formalWeight H e k r = correction c cap H e k r at price
  rw [←price,sub_sub_cancel,formalWeight,if_pos k₀,Complex.ofReal_re]
  rfl

end YM.Integration.WilsonRunMarkedKineticComparison
