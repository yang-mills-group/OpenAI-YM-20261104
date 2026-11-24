import YM.Integration.WilsonSeparatedPrefixMovingCohorts
import YM.WilsonCoeffUV.Product.Report.Charges

/-! A normalized Mer column, inserted on its own date and followed on the
same finite top. The geometric inverse mesh power is its declared height,
uniformly in the number of perturbative coefficients observed. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingOwnDate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{Q:SealR G}{H:Hol G}{e:ℕ}{E W V:Credit}{R:Realm G (e+1) E}

def fee (Q:SealR G)(e:ℕ)(X:Q.Rider):ℝ:=
  ∑ v:Alma Q.F,∑ j:Fin (e+1),‖coeff j.val (X v)‖

/-- All ranks of the true own-date column pay the unshifted coefficient price
before its test is applied. The same chart and complete top are used through
every intervening parent and residue. -/
theorem column (fund:PassportC H R Q W V)(t i N u:ℕ)(origin:R.anchor ≤ t)
    (after:t ≤ i)(cap:i ≤ N)(Z:ℝ)(clock:Compar R.draws.S R.y t i ≤ Z)
    (X:Q.Rider)(φ:Rarity Q.D)(y:ℝ)(o:CellR)(P:Patch)(B:ℝ)(profile:Amplitude φ B):
    let x:=paceT R.draws.S t i
    let α:=(polarBill H Q.ans Q.path e u E W V).choose
    Income (locale o (Q.spins R.draws R.paid φ t i N y X)) Q.h e u
      (OrbP P φ x y o) (charge φ u Q.h x y (α.buy Z*fee Q e X) B):=by
  intro x α
  let δ:=max 0 (R.tempC i i)
  have fp:0≤fee Q e X:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have same:Terms e Q (fee Q e X) δ X X:=by
    intro j hj v
    have cash:‖coeff j (X v)‖≤fee Q e X:=
      (Finset.single_le_sum (f:=fun n:Fin (e+1)=>‖coeff n.val (X v)‖)
        (fun _ _=>norm_nonneg _) (Finset.mem_univ (⟨j,by omega⟩:Fin (e+1)))).trans
        (Finset.single_le_sum (f:=fun v:Alma Q.F=>∑n:Fin (e+1),‖coeff n.val (X v)‖)
          (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ v))
    exact twain.one _ _ (le_max_left _ _) cash
  let tower:=polarP R.draws R.paid Q.ans Q.path N t i X
  have authenticate:On Q.h tower:=by
    dsimp only [tower]
    rw [←fund.lands,←fund.modes]
    exact tournure fund.f.arch X (fund.tap.symm ▸ (origin.trans after)) cap
  have ranks (j:ℕ)(hj:j≤e)(r:ℕ):Fruit 0 1 u (tower.2 j r) (α.buy Z*fee Q e X):=
    (surSeen fund origin after le_rfl cap cap clock fp (le_max_right 0 _) X X same u j hj r).wax
  exact submitted tower authenticate _ ranks φ x y o Q.h P (pace_pos ..) (pace_le _ after) profile

/-- The source salary exhibits exactly one engineering factor per field. -/
theorem units {d:ℕ}(φ:Rarity d)(h u:ℕ)(x y A B:ℝ):
    charge φ u h x y A B=(x^h)⁻¹*((5*radiusH φ x y)^4*(9^u*(B*A))):=by
  unfold charge BasePrice
  ring

end YM.Integration.WilsonSeparatedPrefixMovingOwnDate
