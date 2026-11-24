import YM.Integration.FVA1Physical.Wilson.BoundarySources
import YM.Integration.FVA1Physical.Wilson.ScenePrice
import YM.Integration.FVA1Physical.Round2.VacuumLocality

/-! Complete, period-uniform connected rows for actual boundary noise tilts.
Disjointly supported tilts are honest products of separate insertions in
the joint conditional measure. Their connected generating function is
compared on its whole field ball before taking any rooted derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff

private theorem drop_const {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E→ℝ) (c:ℝ) (l:List E) (i:E) :
    roc (fun x=>f x-c) (i::l) = roc f (i::l) := by
  induction l generalizing i with
  | nil => funext x; change fderiv ℝ (fun y=>f y-c) x i = fderiv ℝ f x i; rw [fderiv_sub_const]
  | cons j js ih => funext x; rw [roc,roc,ih j]

private theorem recenter_rows {ι : Type} [Fintype ι] {c:Side} {s q:ℕ} {w a B:ℝ}
    {site : ι → Site c} {U : Set (Positions ι)} {f : Positions ι→ℝ} (J : JetTab site a s w U f q B) (C : ℝ) :
    JetTab site a s w U (fun x=>f x-C) q B := by
  obtain ⟨hp,price,bill,cost⟩ := J
  refine ⟨hp,price,?_,cost⟩
  intro l hl
  obtain ⟨hP,full⟩ := bill l hl
  refine ⟨hP,?_⟩
  intro x hx
  cases l with
  | nil => simp at hl
  | cons i is => change |roc (fun x=>f x-C) (bolt i::is.map bolt) x| * _ ≤ _; rw [drop_const]; exact full x hx

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path) {N n j k r : ℕ} (S : Scene C.path.levels n r)
    (T : Slices C.path.levels n) (hj : j ≤ N) (h : (traversal T hj).Room G) (tag : (traversal T hj).Tags)
local notation "X" => Positions (Primary (C.side j n) G)

/-- Independent formal log partition at this boundary field, computed from the
FVA2 ledger. The evaluated physical retained density never enters the coefficients. -/
def boundaryBank (p : ℕ) (g : ℝ) (x : X) : ℝ :=
  let A := variedVacuum (traversal T hj) L.O tag h (formalSceneClock S N j) (chartPins G _ x)
  ∑ i ∈ range (p+1), g^i * Wave.bill (Real.log ∘ peval (term A) r) i

/-- The connection is through the true expected product of exponential insertions at
fixed incoming base, before taking its log; this resolves the conditional denominator. -/
def connectedBoundaryError (p : ℕ) (g : ℝ) (base x : X) : ℝ :=
  Real.log (boundaryRead (traversal T hj) (line C.path n j N) (palace (g • base)) (palace (g • x))) -
    (boundaryBank L S T hj h tag p g x - boundaryBank L S T hj h tag p g base)

theorem centered_boundary_error (sel : C.path.Selected) (p : ℕ) (g : ℝ) (base : X) :
    connectedBoundaryError L S T hj h tag p g base = fun x=>
      sceneVacuumError L S T hj h tag p g x - sceneVacuumError L S T hj h tag p g base := by
  funext x
  let Q := C.path.rep N n j
  have pos v : 0 < Q.eval v := SectorNext.Vacuum.strictly C.path sel N n j hj v
  rw [connectedBoundaryError,boundary_read_eq _ (traversal_ok T hj),vacuum_eq T sel hj,
    Real.log_div (pos _).ne' (pos _).ne']
  change (Aqua.vine Q g x - Aqua.vine Q g base) - _ = (_-boundaryBank L S T hj h tag p g x)-(_-boundaryBank L S T hj h tag p g base)
  ring

/-- A cofinal ultraviolet cutoff is chosen before every period, history, boundary
base, and independent test of each complete row of connected response coefficients. -/
theorem uniform_connected_boundary (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m q : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p+3 ≤ m) (hq : q+1 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j ≤ N, ∀ (T : Slices C.path.levels n)
        (h : (traversal T hj).Room G) (tag : (traversal T hj).Tags) (base : Positions (Primary (C.side j n) G)),
        let β := C.path.levels.clock.hatBeta j
        let g := Heath.Stock.cue (C.path.rep N n j).beta
        let w := Mosaic.vol β
        JetTab (Measuring.chart _ G) (Mosaic.αm β) s w (Metric.closedBall 0 w)
          (connectedBoundaryError L S T hj h tag p g base) q (g^((p:ℝ)+1-η)) := by
  filter_upwards [uniform_ledger_envelope L u simple sel D s p m q hs hm hp hq hη] with k bought
  intro N n lo
  obtain ⟨S,hS,rows,_⟩ := bought N n lo
  refine ⟨S,hS,?_⟩
  intro j hj hjN T h t b
  dsimp only
  rw [centered_boundary_error L S T hjN h t sel]
  exact recenter_rows (rows j hj hjN T h t) _

end YM.Integration.FVA1Physical.Wilson
