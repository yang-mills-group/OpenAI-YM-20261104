import YM.Integration.WilsonOriginalCopiedMarkerLayout

/-! At the original period, a copied curvature word has the original marked radial coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSelfPeriod
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open private parts from YM.Integration.WilsonOriginalMixedFiniteMaterial
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open FVA1Physical.TwoReset
open Function Filter Macrame Shingle
open scoped Classical BigOperators Topology


private theorem site {n : Side} (v : Site n) (u : Fin (Pages n n)) :
    (page (dvd_refl n.val) v u).val = v := by
  classical
  let h := dvd_refl n.val
  have fixed (s : Site n) : splitter h s = s := by
    calc
      _ = splitter h (wrap n (lift s)) := congrArg (splitter h) (wrap_lift s).symm
      _ = wrap n (lift s) := branch h (lift s)
      _ = s := wrap_lift s
  apply (fixed _).symm.trans
  have member := (page h v u).property
  simpa only [Shingle.parcel, Finset.mem_filter, Finset.mem_univ, true_and] using member

theorem original {G : Gauge} {V ι α : Type} [DecidableEq V] [Fintype V] {n : Side}
    {P : Earn.Passport n V} {r : Census V} (M : ι → Row P r G α) (wts : V → ℕ)
    (L : Layout G) (T : Finset Age) (test : α) (d : ℕ) (y : Stationary.Link G n)
    {a : ℝ} {k : ℕ} (staff : Air.Staff M (fun j=>(M j).paint test) wts a k) :
    peek (dvd_refl n.val) M wts L T test d y =
      Air.discharge (Air.craft M (fun j=>(M j).paint test) wts L T) d (Stationary.arm G n 1 y) := by
  classical
  let h := dvd_refl n.val
  let w j := (M j).paint test
  have active (j : ι) (u : Fin (Pages n n)) :
      (FVA1Physical.TwoReset.copy h (M j) u).markReceipt d y=(M j).markReceipt d y := by
    unfold Row.markReceipt
    simp only [recenter, site]
    rfl
  have same (j : ι) : (∑ u : Fin (Pages n n), reading h M test y d j u) =
      Poly.send (M j).mode (w j * ((M j).markReceipt d y : ℂ)) := by
    calc
      _ = ∑ _u : Fin (Pages n n), Poly.send (M j).mode
          (w j * ((M j).markReceipt d y : ℂ)) := by
        apply Finset.sum_congr rfl
        intro u _
        unfold FVA1Physical.TwoReset.reading
        rw [active]
      _ = _ := by simp [Pages]
  exact ((total_peek h M wts L T test y d staff).congr_fun (fun j=>(same j).symm)).unique
    (Air.compared M w wts staff L T y d)

end YM.Integration.WilsonOriginalSelfPeriod
