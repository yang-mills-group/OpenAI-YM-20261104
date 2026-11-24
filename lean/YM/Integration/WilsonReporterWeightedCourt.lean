import YM.Integration.WilsonReporterWeightedMarket
import YM.Integration.WilsonPhysicalThermalWickHearing

/-! Uniform physical chamber membership and the actual original Wick chart
on a scheduled two-name course. The enclosure is the finite-stencil argument
of Prom.Hill.Coordinates, with its placement quantifier moved after N. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedCourt
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Function Filter Set Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open scoped Topology BigOperators Classical
variable {G:Gauge} {F:Family G} {k:ℕ} {b:ℝ}
theorem enclosure (d : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ hN : k≤N, ∀ p : ℕ, ∀ z ∈ (F.localSection d).stencil,
    ∀ j : Axis,
      let A := F.path.levels
      let T := center F.S p (((widerSky A b k).trans (beforeSky A b k)).trans hN) 0
      (z j).natAbs<T.side.val/8 := by
  let l := widthSky F.path.levels b k
  have he (z : Cover) (i : Axis) : ∀ᶠ N in atTop, F.S.a N * (↑(8*((z i).natAbs+1)):ℝ) ≤ F.S.a l := by
    have hv := F.S.shrinks.mul_const ((8*((z i).natAbs+1):ℕ) : ℝ); rw [zero_mul] at hv
    exact hv.eventually (ge_mem_nhds (F.S.a_pos l))
  have hs := eventually_all_finset _|>.2 (fun z (_:z∈(F.localSection d).stencil) => eventually_all.mpr (he z))
  filter_upwards [eventually_ge_atTop k,hs] with N hN h
  refine ⟨hN,fun p z hz i => ?_⟩
  intro A T
  have hh := h z hz i
  have ht : F.S.a N * ((8*((z i).natAbs+1):ℕ):ℝ) ≤ F.S.a N*T.side.val := hh.trans_eq (F.S.embeds_scale T.units).symm
  have hv : 8*((z i).natAbs+1) ≤ T.side.val := by exact_mod_cast (le_of_mul_le_mul_left ht (F.S.a_pos N))
  omega


theorem inside (H : F.Makes) {n : ℕ} (d : Fin n→ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p:ℕ) (live:k≤N) (x:Points n) (_:FitSky F.path.levels b k x)
      (v:(i:Fin n)→F.label (d i)) (j:Fin n),
    Interior ((Ship.yardSky F b live p).chamber 0)
      (Read.probes F N p k (Station.choose F.path.levels b k x) (q_asked (C:=F) v) j) := by
  filter_upwards [eventually_all.mpr (fun j=>enclosure (F:=F) (k:=k) (b:=b) (d j))] with N covered
  intro p live x fit v j
  obtain ⟨_,bounds⟩ := covered j
  exact Extraction.Around.figure H _ ⟨_,v j⟩ _ _ (fit.margin p live j) (bounds p)

variable {C : Family G} {u D N p : ℕ} {w l z r : ℝ} {α : Purse}
    (B : Binding C) (H : C.Makes) {O : HaarBudget G} (J : ChartRatio G)
    {dg:Fin 2→ℕ} {v : (i:Fin 2)→C.label (dg i)} {x:Points 2} {K:Set (Points 2)}
local notation "AX"=>C.path.levels

theorem original (L : LegacyCostSky B J w z α k u D O l r) (fine : k<N)
    {P:(i:ℕ)→Rep G (C.side i p)}
    (F₀ : WhipSky B J α L.hours L.moves (isohypse H fine.le p) P (Station.widthSky AX α.band k) le_rfl)
    (hpos : 0≤α.band) (grade : C.ref D≤k) (two : 2≤u)
    (model : Radian.Seal AX k p D 2 (PhysicalNext.RankCovariance.stamp AX N p) chartHeat →
      Wall.Model AX D k p (PhysicalNext.RankCovariance.stamp AX N p))
    (hY : ∀ i,dg i≤D) (held : WallsSky α.band hY v K α.taylor k)
    (hx : tested AX α.band k x∈K) (fit : FitSky AX α.band k x) :
    BalconSky α.band hY v x k α.taylor ∧
      BellSky AX (PhysicalNext.RankCovariance.stamp AX N p) D α.taylor fit ∧
      invariantAt (C:=C) k (wood AX k) p (PhysicalNext.RankCovariance.stamp AX N p) := by
  let history := isohypse H fine.le p
  have native := embroideredSky B J history α H L.hours L.token L.moves P F₀ hpos
  have served := v_ceremonySky native L.moves.coup
  have allowed := L.age.allot.permitted
  have stage : D-1 ≤ C.path.levels.clock.J k-1-2 := by
    have h := (H.stages D).1; have h' := (C.path.levels).fits.mono grade; omega
  obtain ⟨sealed_,pay⟩ := y_supplySky _ _ rfl allowed stage L.clears N p
  let chart := pay 2 two
  obtain ⟨Q,hS,hA,hP⟩ := chart.optics
  have seen : Wall.VantageSky AX D k p 2 α.taylor α.band (PhysicalNext.RankCovariance.stamp AX N p) :=
    ⟨model sealed_,Radian.flownSky _ _ _ _ _ hS hP hA chart.visor chart.hinge chart.rotor chart.force⟩
  exact ⟨held.merry x hx,(held.replies x hx fit allowed).2 _ _ seen,served.invariant⟩

end YM.Integration.WilsonReporterWeightedCourt
