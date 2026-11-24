import YM.Integration.WilsonEpochScaleReports

/-! Smeared comparison at every real subtraction scale on one mesh event,
with the original first-derivative norm of the test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochUniformReports
open Function Filter Set Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register MS MS.Land
open scoped Topology BigOperators Classical

theorem measured {G : Gauge} {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
    {n d : ℕ} (p : Tags G d n) (k : ℕ) (K : Set (Points n)) (hK : IsCompact K)
    (hs : K ⊆ conf n) :
    ∃ C : ℝ, 0<C ∧ ∃ e : ℕ, ∀ᶠ m in Front, ∀ f : Test n, tsupport f ⊆ K →
      ∀ b : ℝ, TestBudget.Bound f b → ∀ ν : ℝ,
      ‖Reg.Pivot.posted ν Z.scheme S d m k n f p - Reg.CoverTest.Rates ν T d k n f p‖ ≤
        b*(C*(1+|ν|)^e*m.spacing^MS.Tide.mildG) := by
  obtain ⟨N,A,hA,e,quote⟩ := MSExteriorFiniteScales.finite_observations
    (WilsonEpochScaleReports.original Z M p k)
  choose costs pos attend using
    (fun j : Fin N => (M.exactbreg (j.val : ℝ) n d k p K hK hs).2)
  let D : ℝ := 1+∑ j : Fin N,costs j
  have sum0 : 0 ≤ ∑ j : Fin N,costs j := Finset.sum_nonneg (fun j _ => (pos j).le)
  have hD : 0<D := by unfold D; linarith
  have below (j : Fin N) : costs j ≤ D := by
    have h := Finset.single_le_sum (s:=Finset.univ) (f:=costs) (fun i _ => (pos i).le)
      (Finset.mem_univ j)
    unfold D
    linarith
  refine ⟨(1+A)*D,mul_pos (by linarith) hD,e,?_⟩
  filter_upwards [Filter.eventually_all.mpr attend] with m hm f near b hf ν
  have hb : 0 ≤ b := (norm_nonneg _).trans (hf 0).1
  have s0 : 0 ≤ m.spacing^MS.Tide.mildG := Real.rpow_nonneg m.positive.le _
  have price := quote (m,f) ν (b*D*m.spacing^MS.Tide.mildG) (by positivity)
    (fun j hj => by
      let i : Fin N := ⟨j,Finset.mem_range.mp hj⟩
      have hi := hm i f near b hf
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (below i) hb) s0))
  refine price.trans ?_
  have p0 : 0 ≤ (1+|ν|)^e := by positivity
  calc
    A*(1+|ν|)^e*(b*D*m.spacing^MS.Tide.mildG) ≤
      (1+A)*(1+|ν|)^e*(b*D*m.spacing^MS.Tide.mildG) := by
        gcongr
        linarith
    _ = _ := by ring

end YM.Integration.WilsonEpochUniformReports
end
