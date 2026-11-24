import YM.Integration.ActualFoundryDetectorSource
import YM.Integration.ActualSignedCore
import YM.Push.STRESS_FLUX.Matching

/-! Exact physical placement and normalization of the complete detector.
The central discrepancy and every exterior field keep their own sites.
The same full marked numerator is transported and then averaged against
the actual coarse law; no product of conditional means is introduced. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualFoundryDetectorSource
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent MergeProof.Replicum Extra.Histories Extra.Trajectories
open NativeSignedBranches StressFlux.Matching OPE.Therm
open scoped Classical BigOperators

variable {G : Gauge} {E : Type} [Fintype E] [DecidableEq E] {arity : ℕ}

/-- Dummy unit and zero entries keep explicit sites in their own region. -/
def positions (x : Fin (arity + 1) → E4) (y : E → E4) (a : Slot arity E) : E4 :=
  match a.1.1 with
  | Sum.inl _ => if a.1.2 then x a.2 else 0
  | Sum.inr i => y i

def origins (C : Family G) (p : ℕ)
    (x : Fin (arity + 1) → E4) (y : E → E4) :
    ∀ m, Slot arity E → Site (C.side m p) :=
  fun m a => ceilSite C m p (positions x y a)

/-- Both complete physical terms retain the identical exterior product. -/
def physical (C : Family G) (N p : ℕ)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (x : Fin (arity + 1) → E4) (y : E → E4) :
    Config G (C.side N p) → ℂ := fun U =>
  ((∏ j, C.O N p (v j).2 (ceilSite C N p (x j)) U) -
    C.O N p z.2 (ceilSite C N p 0) U) *
    ∏ i, C.O N p (e i).2 (ceilSite C N p (y i)) U

def numerator (C : Family G) (N p : ℕ)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (unitDegree zeroDegree : ℕ)
    (x : Fin (arity + 1) → E4) (y : E → E4) :
    Config G (C.side N p) → Poly (Bud (Region E)) :=
  fun U => compress (source C N p v z e unitDegree zeroDegree
    (origins C p x y) (fun _ => (1, false)) U)

private theorem item_identity (C : Family G) (N p d : ℕ) (v : C.label d)
    (o : ∀ m, Site (C.side m p)) :
    item C d N p v o (1, false) = C.O N p v (o N) := by
  funext U
  unfold item stepUp
  dsimp only
  rw [pull_one]
  change C.O N p v 0 (translate (o N) U) = _
  simpa using C.translation 0 (o N) v U

variable (C : Family G) (hC : C.Makes) (N p : ℕ)
    (v : Fin (arity + 1) → (d : ℕ) × C.label d)
    (z : (d : ℕ) × C.label d) (e : E → (d : ℕ) × C.label d)
    (unitDegree zeroDegree : ℕ) (hUnit : C.ref unitDegree ≤ N)
    (x : Fin (arity + 1) → E4) (y : E → E4)

include hC hUnit in
theorem numerator_final (U : Config G (C.side N p)) :
    (numerator C N p v z e unitDegree zeroDegree x y U).part (Stock.final (Region E)) =
      (C.path.rep N p N).eval U * physical C N p v z e x y U := by
  have hF : centralFactors C N p v (origins C p x y) (fun _ => (1, false)) =
      fun j => C.O N p (v j).2 (ceilSite C N p (x j)) := by
    funext j
    exact item_identity C N p (v j).1 (v j).2 _
  have hK : centralCounter C N p z (origins C p x y) (fun _ => (1, false)) =
      C.O N p z.2 (ceilSite C N p 0) := item_identity C N p z.1 z.2 _
  have hE : exteriorFields C N p e (origins C p x y) (fun _ => (1, false)) =
      fun i => C.O N p (e i).2 (ceilSite C N p (y i)) := by
    funext i
    exact item_identity C N p (e i).1 (e i).2 _
  unfold numerator
  rw [full_coefficient C N p v z e unitDegree zeroDegree _ _ hC hUnit,
    hF, hK, hE]
  rfl

include hC in
theorem numerator_integrable :
    Integrable (numerator C N p v z e unitDegree zeroDegree x y) (prior G _) := by
  apply (compress.restrictScalars ℝ).integrable_comp
  exact PhysicalJoin.Marked.topLive _ _ (origins C p x y)
    (fun _ => (1, false)) hC _ N

omit [DecidableEq E] in
private theorem physical_continuous : Continuous (physical C N p v z e x y) :=
  ((continuous_finsetProd _ (fun j _ => C.continuousO N p (v j).1 (v j).2 _)).sub
    (C.continuousO N p z.1 z.2 _)).mul
    (continuous_finsetProd _ (fun i _ => C.continuousO N p (e i).1 (e i).2 _))

include hC hUnit in
/-- The coarse normalized readout is the original complete detector moment.
All fields, the partition, and the trajectory belong to the same family. -/
theorem normalized_mean {m : ℕ} (hm : m ≤ N) :
    (∫ U, (actualSignedTransport C (N := N)
        (numerator C N p v z e unitDegree zeroDegree x y) hm U).part
        (Stock.final (Region E)) ∂scene C.path N p m) =
      moment (C.beta N p) (physical C N p v z e x y) := by
  rw [actualSignedTransport_coefficient_mean C hC (le_refl N)
    (numerator_integrable C hC N p v z e unitDegree zeroDegree x y) hm]
  simp_rw [numerator_final C hC N p v z e unitDegree zeroDegree hUnit x y,
    (hC.wilson.starts N p).2]
  rw [moment_formula _ _ (continuous_integrable _
    (physical_continuous C N p v z e x y))]
  simp only [Complex.real_smul, Complex.ofReal_inv]

end YM.Integration.ActualFoundryDetectorSource
