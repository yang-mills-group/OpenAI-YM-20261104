import YM.Integration.WilsonOriginalAlternativeTrialNet
import YM.Integration.WilsonOriginalAlternativeGuard
import YM.Integration.WilsonOriginalAlternativeTrialWallet
import YM.Integration.WilsonThermometerSameWalkSectionFare

/-! Uniform group-field bound for each actual tuned guard at its common K birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialGuardField
open Filter Function Finset Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn
open PhysicalNext.Repeat.Legato Push.Local Push.AbsoluteSums AnalyticNext WilsonRetainedMarkedInletRegular
open ActualRunPhysicalPages ActualRunCurvaturePackets
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) {V:Type} [DecidableEq V] [many:Fintype V] (d:V→ℕ)
local notation "C₀" => R.family
local notation "β" j:max => (C₀).path.levels.clock.hatBeta j
open WilsonOriginalAlternativeTrialWallet

include many in
/-- On each original cutoff field the full tuned guard is bounded before the
regulator. This is the paid guarded field itself, including its unit component. -/
theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (forecast:WilsonReportLampForecast.Ready (C₀).path.levels):
    ∀ᶠ K:ℕ in atTop,∀N per:ℕ,K ≤ N→(∀j,(C₀).ref (d j) ≤ K)→
      ((C₀).path.levels.params K).supportExponent=100 →
      ∀(o:V→Site ((C₀).side K per))(v:∀j,(C₀).label (d j))(z:V→ℂ)(j:V)(U:Config G ((C₀).side K per)),
      ‖WilsonOriginalAlternativeTrialSource.arm R d N per K o v z j U‖ ≤
        (β K)^6*((C₀).labels.level (d j)).coeffSize (z j • v j):=by
  have prices:∀ᶠ K:ℕ in atTop,∀j:V,∀N per:ℕ,K ≤ N→((C₀).path.levels.params K).supportExponent=100 →
      ∀(o:V→Site ((C₀).side K per))(v:(C₀).label (d j)),
      WilsonOriginalStarPrimaryCatalog.rent R N per K (d j) o j v (fun _=>1) (100+1+1) ≤
        (β K)^6*((C₀).labels.level (d j)).coeffSize v:=by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [WilsonThermometerSameWalkSectionFare.original R (d j) simple pace forecast] with K cash
    intro N per live base o v
    simpa only [one_mul] using cash N per live base o j v (fun _=>1) zero_le_one
  filter_upwards [prices] with K rates N per live ref base o v z j U
  let J:=Stock.census V
  let P:=(C₀).path.rep N per K
  let t:=fun _:Unit=>(1:ℂ)
  let w:=fun _:V=>(1:ℝ)
  let next:=fun a=>z a • v a
  let L:=WilsonOriginalStarPrimaryCatalog.catalogue (J:=J) R N per K (d j) live (ref j) o j (next j) t
  have rent:=WilsonOriginalStarPrimaryCatalog.funded (J:=J) R N per K (d j) live (ref j) o j (next j) t w
    (fun _=>zero_lt_one) (100+1+1) (fun _=>by simp [t])
  have bill:=WilsonFirstReceivedGalleryRegular.occupied (P:=P) L rent (by norm_num) (fun _=>zero_lt_one) () U
    (J.fire j) j (Finset.mem_singleton_self j)
  rw [Poly.solo_toll,WilsonOriginalStarPrimaryCatalog.filed] at bill
  have id:=WilsonOriginalAlternativeHosted.primary R N per K o d next (fun (_:Unit)(_ : V)=>(1:ℂ)) P rfl () U j
  change (1:ℂ)*WilsonOriginalStarPrimaryCatalog.primary R N per K (d j) o j (next j) U=
    (1:ℂ)*Extra.Histories.part (R.family.localSection (d j)) (o j) P U (z j • v j) at id
  rw [LinearMap.map_smul,smul_eq_mul] at id
  change ‖z j*Extra.Histories.part (R.family.localSection (d j)) (o j) P U (v j)‖≤_
  simp only [t,w,one_mul] at id bill
  rw [←id]
  exact bill.trans (rates j N per live base o (next j))

end YM.Integration.WilsonOriginalAlternativeTrialGuardField
end
