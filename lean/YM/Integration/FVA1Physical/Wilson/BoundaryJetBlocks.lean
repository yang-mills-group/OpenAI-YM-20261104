import YM.Integration.FVA1Physical.Wilson.BoundaryBlocks
import YM.Integration.FVA1Physical.Round2.CalibratedJetShells

/-! Spatial localization of the whole held derivative row for a finite product
of actual coarse-boundary insertions, relative to its independent Wilson series. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16 Pressure
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff
variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path) {N n j k r : ℕ} (S : Scene C.path.levels n r)
    (T : Slices C.path.levels n) (hj : j < N) (h : (traversal T hj.le).Room G) (t : (traversal T hj.le).Tags)
local notation "X" => Positions (Primary (C.side j n) G)

/-- The product of the separate physical insertions is taken before Haar
integration and tag averaging. The independent polynomial uses one common history. -/
def blockError {ι : Type} [DecidableEq ι] (A : Finset ι) (K : ι → Finset (Bond (C.side j n)))
    (p : ℕ) (g : ℝ) (base x : X) : ℝ :=
  Real.log (blockRead (traversal T hj.le) (line C.path n j N) A K (palace (g • base)) (palace (g • x))) -
    (boundaryBank L S T hj.le h t p g x - boundaryBank L S T hj.le h t p g base)

theorem block_error_eq {ι : Type} [DecidableEq ι] (A : Finset ι) (K : ι → Finset (Bond (C.side j n)))
    (he : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint (K a) (K b)) (hc : A.biUnion K=univ)
    (p : ℕ) (g : ℝ) (base : X) :
    blockError L S T hj h t A K p g base = connectedBoundaryError L S T hj.le h t p g base := by
  funext x
  unfold blockError connectedBoundaryError
  congr 2
  rw [traversal_push T hj]
  exact block_read_cover (T j) (traversal T hj) _ A K he hc _ _

/-- For every cutoff in the same cofinal set the entire row of connected marked
derivatives is exponentially insensitive to remote boundary fields. The sum includes
all choices of the remaining q addresses and costs nothing for the number of groups. -/
theorem uniform_block_localization (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (D : Docket C u L.O L.horizon L.kin) (s p m q : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m)
    (hp : p + 3 ≤ m) (hq : q + 2 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k ≤ j → ∀ hj : j<N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj.le).Room G)
        (t : (traversal T hj.le).Tags) (ι : Type) [DecidableEq ι] (A : Finset ι) (K : ι → Finset (Bond (C.side j n))),
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint (K a) (K b)) → A.biUnion K=univ →
        ∀ base : Positions (Primary (C.side j n) G),
        let β := C.path.levels.clock.hatBeta j
        let w := Mosaic.vol β
        let a := Mosaic.αm β
        let g := Heath.Stock.cue (C.path.rep N n j).beta
        let E := blockError L S T hj h t A K p g base
        let site := Measuring.chart (C.side j n) G
        ∀ x∈Metric.closedBall 0 w, ∀ i R, Yarn q (fun l =>
          |buoy E x (i::l) - buoy E (Round2.nearField site i R x) (i::l)| * Measuring.swipe site (a/2) s (i::l)) ≤
          g^((p:ℝ)+1-η) / w^(q+1) / liftW (a/2) 0 (R+1) := by
  have grows := Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨k₀,h₀⟩ := eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [uniform_connected_boundary L u simple sel D s p m (q+1) hs hm hp (by omega) hη,
    D.purse s (p+1) m hs hm hp,eventually_ge_atTop k₀] with k bought purse cut
  intro N n lo
  obtain ⟨S,hS,rows⟩ := bought N n lo
  have checks := ((purse N n lo).2 S hS).1
  refine ⟨S,hS,?_⟩
  intro j hk hj T h t ι _ A K he hc base β w a g E site x hx i R
  let Q := C.path.rep N n j
  have eqn : E = connectedBoundaryError L S T hj.le h t p g base := block_error_eq L S T hj h t A K he hc p g base
  rw [eqn]
  have wide := h₀ j (cut.trans hk)
  have hw : 0 < w := div_pos wide (by norm_num)
  have ha : 0 ≤ a := zpow_nonneg wide.le _
  have smooth (y : Positions (Primary (C.side j n) G)) (hy : y∈Metric.closedBall 0 w) :
      ContDiffAt ℝ (m+1:ℕ) (connectedBoundaryError L S T hj.le h t p g base) y := by
    rw [centered_boundary_error L S T hj.le h t sel]
    apply ContDiffAt.sub _ contDiffAt_const
    rw [←sceneVacuumError_eq L S T hj.le h t hS hk (Nat.le_succ p)]
    have top := (checks j hk hj.le).grown y hy
    have poly (q : ℕ) := (Aqua.pure Q (S.Poly j) g q).contDiffAt (x:=y)
    have source : ContDiffAt ℝ (m+1:ℕ) (Aqua.vine Q g) y := by
      have core := top.add ((poly (p+1)).of_le le_top)
      convert core using 1
      funext z; change Aqua.vine Q g z = (Aqua.vine Q g z - _) + _; abel
    exact source.sub ((poly p).of_le le_top)
  exact Round2.rooted_jet_near (rows j hk hj.le T h t base) hw ha smooth (by omega) i R hx

end YM.Integration.FVA1Physical.Wilson
