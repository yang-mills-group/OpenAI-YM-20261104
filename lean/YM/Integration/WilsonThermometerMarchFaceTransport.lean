import YM.Integration.WilsonPositionThermometerDepositedFaces

/-! Restoring one fixed marked placement weight commutes with every
original Wilson conditional on the full unnormalized numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchFaceTransport
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open RG05Readout Records Native Address Many Marker MergeProof MergeProof.Accent
open scoped Topology Classical BigOperators
variable {G : Gauge} (C : Family G) {N p j : ℕ}

theorem scaled (f : Config G (C.side N p) → ℂ) (w : ℂ)
    (paid : Integrable f (prior G _)) (hj : j ≤ N) :
    gust C.path N p N (w • f) j hj = w • gust C.path N p N f j hj := by
  induction hj using Nat.decreasingInduction with
  | self => rw [gust_base,gust_base]
  | of_succ i hi rest =>
    rw [gust_step _ _ _ _ _ hi, gust_step _ _ _ _ _ hi, rest]
    exact (C.path.levels.clock.op i p).push_smul _ _ _ (gust_live _ _ _ _ _ paid hi)

/-- The two complete inputs may carry arbitrary other occupied subwords. -/
theorem restored {I : Type} [DecidableEq I] {J : Census I}
    (K L : Config G (C.side N p) → Poly J) (s : J.Mode) (w : ℂ)
    (hK : Integrable K (prior G _)) (hL : Integrable L (prior G _))
    (leg : (fun U => (K U).part s) = w • (fun U => (L U).part s)) (hj : j ≤ N) :
    (fun U => (gust C.path N p N K j hj U).part s) =
      w • (fun U => (gust C.path N p N L j hj U).part s) := by
  rw [pushpart hj K s hK, pushpart hj L s hL,leg]
  exact scaled C _ _ ((Poly.get s).integrable_comp hL) hj

end YM.Integration.WilsonThermometerMarchFaceTransport
