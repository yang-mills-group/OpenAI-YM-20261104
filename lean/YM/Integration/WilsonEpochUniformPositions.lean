import YM.Integration.WilsonEpochScalePolynomials

/-! A common compact-separated cutoff event for all real subtraction scales.
The explicit price is polynomial in the scale, using only genuine sampled
historical coefficients and their independent MS targets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochUniformPositions
open Function Filter Set Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register MS MS.Land
open WilsonEpochScalePolynomials
open scoped Topology BigOperators Classical

theorem measured {G : Gauge} {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
    {n d : ℕ} (p : Tags G d n) (k : ℕ) (K : Set (Points n)) (hK : IsCompact K)
    (hs : K ⊆ conf n) :
    ∃ C : ℝ, 0<C ∧ ∃ e : ℕ, ∀ᶠ m in Front, ∀ v : Sample n,
    v.F=m → welcome v → familiar v ∈ K → ∀ ν : ℝ,
      ‖Dframe.postedPoint ν Z.scheme S d v k p - Dframe.meteor ν T d (familiar v) k p‖ ≤
        C*(1+|ν|)^e*m.spacing^MS.Tide.mildG := by
  obtain ⟨N,A,hA,e,quote⟩ := MSExteriorFiniteScales.finite_observations
    (WilsonEpochScalePolynomials.original Z M p k)
  choose costs pos attend using
    (fun j : Fin N => (M.exactbreg (j.val : ℝ) n d k p K hK hs).1)
  let D : ℝ := 1+∑ j : Fin N,costs j
  have sum0 : 0 ≤ ∑ j : Fin N,costs j := Finset.sum_nonneg (fun j _ => (pos j).le)
  have hD : 0<D := by unfold D; linarith
  have below (j : Fin N) : costs j ≤ D := by
    have h := Finset.single_le_sum (s:=Finset.univ) (f:=costs) (fun i _ => (pos i).le)
      (Finset.mem_univ j)
    unfold D
    linarith
  refine ⟨(1+A)*D,mul_pos (by linarith) hD,e,?_⟩
  filter_upwards [Filter.eventually_all.mpr attend] with m hm v hv hot near ν
  let v' : Good n := ⟨v,hs near⟩
  have s0 : 0 ≤ m.spacing^MS.Tide.mildG := Real.rpow_nonneg m.positive.le _
  have price := quote v' ν (D*m.spacing^MS.Tide.mildG) (mul_nonneg hD.le s0)
    (fun j hj => by
      let i : Fin N := ⟨j,Finset.mem_range.mp hj⟩
      have hi := hm i v hv hot near
      change ‖Dframe.postedPoint (j:ℝ) Z.scheme S d v k p -
        Dframe.meteor (j:ℝ) T d (familiar v) k p‖ ≤ _
      rw [show Speed.chip v.F = m.spacing^MS.Tide.mildG by rw [hv]] at hi
      exact hi.trans (mul_le_mul_of_nonneg_right (below i) s0))
  refine price.trans ?_
  have p0 : 0 ≤ (1+|ν|)^e := by positivity
  calc
    A*(1+|ν|)^e*(D*m.spacing^MS.Tide.mildG) ≤
      (1+A)*(1+|ν|)^e*(D*m.spacing^MS.Tide.mildG) := by
        gcongr
        linarith
    _ = _ := by ring

end YM.Integration.WilsonEpochUniformPositions
end
