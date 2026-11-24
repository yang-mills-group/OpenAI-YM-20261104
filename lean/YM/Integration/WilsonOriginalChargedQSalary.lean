import YM.Integration.WilsonOriginalChargedSourceHead

/-! The declared Laurent order changes on the same independent Q source. All finite and covered positions keep their original prepaid collision and path prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedQSalary
open Function Finset Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Mosaic.Near
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address RG05Readout.Native
open Extra.Histories
open ActualRunCalibrationTests NativeCurvatureTensor ActualRunKernelPackets ActualRunCurvaturePackets
open OriginalSourceJetAddresses OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Classical BigOperators

open FundedOriginalMarkedInput

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G} {p L n : ℕ} {hn : n ≤ L}
  {V : Type} [Fintype V] [DecidableEq V] (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V) (u : V → MS.Rake.Label B)
  (μ : ℝ) (orders : V → ℕ)

variable (scale:V→ℂ)(comp:V→Bool)
local notation "frozen" => chosen Q D u μ orders scale comp

def pole (i:V)(b:Count D u i) : ℕ := fieldRank R (ActualOriginalQPackets.degree u) b.1.val

def grade (i:V) : ℕ := Finset.univ.sup (pole D u i)

def lowered (i:V)(b:Count D u i) : Seed G (OrbitD D i) :=
  {frozen i b with head:=(frozen i b).rank-pole D u i b}

omit [Fintype V] [DecidableEq V] in
theorem degree (i:V)(b:Count D u i) : pole D u i b≤(frozen i b).rank :=
  term_grade R (ActualOriginalQPackets.degree u) b.1.val

theorem loan (k:V→ℕ)(cap:ℕ)(w:ℝ) :
    bill (lowered Q D u μ orders scale comp) k cap w = bill frozen k cap w :=rfl

theorem funded (k:V→ℕ)(cap:ℕ){w:ℝ}(hw:0<w)(Z:Finset V)(sites:V → Cover) :
    let ranks:=fun i=>max (k i) (grade D u i)
    let A:=lowered Q D u μ orders scale comp
    let B:=bill frozen ranks cap w
    let K:=independent A sites
    0≤B ∧ Eu ranks K ∧ K ∅=0 ∧ safeB sites K Z cap (steep w) B :=by
  intro ranks A B K
  apply preblock A sites Z cap hw
  intro i b
  have rankOK:=degree Q D u μ orders scale comp i b
  have active:pole D u i b≤ranks i :=
    (Finset.le_sup (f:=pole D u i) (Finset.mem_univ b)).trans (le_max_right _ _)
  change (frozen i b).rank ≤ ranks i+((frozen i b).rank-pole D u i b)
  omega

end YM.Integration.WilsonOriginalChargedQSalary
