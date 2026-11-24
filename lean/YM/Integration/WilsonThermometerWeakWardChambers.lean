import YM.Integration.WilsonThermometerWeakWardClearance
import YM.Integration.WilsonThermometerWeakSameRunCross

/-! A common translated pair of original physical cells for the rank detector
and finite equation erasure, including the unrestricted fine spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardChambers
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
open Next.Rank.Price Next.Rank.Tapes.West Next.Rank.Station Next.Rank.East
open Further.CorrectedLift MergeProof MergeProof.East MergeProof.Accent
open PhysicalNext.Repeat.Legato YM.Integration.WilsonLimitConstruction YM.Integration.WilsonPositionThermometerStationNorm
open RG12 RG05Readout Native Address Many Records Harvest
open WilsonThermometerOwnOffsetField WilsonThermometerWeakPanelBorn WilsonThermometerSmallPanelRead
open scoped Topology BigOperators Classical
open WilsonThermometerWeakMovedCovers WilsonThermometerWeakJointWidth
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.alloy.B.a

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) :
    ∃e:ℕ,∀ (a b h:ℝ),0<a → 0<b → power a b e<h →
    ∀(x:Fin 2→E4),(∃j:Axis,x 0 j≠x 1 j) →
    ∀ᶠ k:ℕ in atTop,Allowed (A) b k → wheel (A) k≤(A).clock.monitor k →
    ∀d radius:ℕ,∀ᶠ N:ℕ in atTop,∃hk:k≤N,∀p,
      let hχ:=((wider (A) b k).trans ((before (A) b k).trans hk))
      let T₀:=center (C).S p hχ 0
      ∀(z:Fin 2→Site ((C).side N p)) (q:Fin 2→Lattice.Cover),
      (∀i j,|(C).S.gridPoint k (q i) j-gap (A) h k*x i j|≤16*(C).S.a k) →
      let w:=fun i=>move (C).S p hk (z i) (wrap ((C).side k p) (q i))
      let pivot:=move (C).S p hk (z 1) 0
      ∃(m:ℕ)(hm:m≤k)(t:Site ((C).side N p))(c₀ c₁:Site ((C).side m p)),
      let T:=center (C).S p (hm.trans hk) 0
      c₀≠c₁ ∧ w 0+t∈T.margin c₀ (3*span (C).S hk p) ∧
      ∀(r:Emblems C d)(v:(C).label d),LocalOn (Mark.Outer radius (w 0+t)) (arm R r hk (w 1+t) v) ∧
      ∀a:ℝ, Interior (T₀.chamber 0) (arm R r hk pivot v) → T₀.rootTest ((C).beta N p) (arm R r hk pivot v)≤a →
        ∃Z,Interior (T.chamber 0) Z ∧ T.rootTest ((C).beta N p) Z≤a ∧ T.copy c₁ Z=arm R r hk (w 1+t) v:=by
  obtain ⟨e,housing⟩:=WilsonThermometerWeakJointCells.original (C).S
  refine ⟨e+1,?_⟩
  intro a b h ap bp enough x sep
  let U:=power a b (e+1)
  have Upos:0≤U:=by dsimp [U,power];have wide:=le_max_left (4*(a+5)) (b+5);positivity
  filter_upwards [eventually_ge_atTop 1,WilsonThermometerWeakJointMesh.original R simple shop a b ap bp (e+1),
    WilsonThermometerWeakTwoScalePlacement.fee (A) simple U h Upos enough x sep]
      with k positive bound layout
  intro ok widthPaid d radius
  have nonneg:0≤Real.log ((A).clock.hatBeta k):=Real.log_nonneg ((A).fits.delayed _).le
  have within:(C).S.scale k-(C).S.scale k≤Real.log ((A).clock.hatBeta k):=by simpa only [sub_self] using nonneg
  obtain ⟨side0,side1,income⟩:=bound k le_rfl within ok widthPaid
  let χ:=width (A) b k
  let m:=min (widthSky (A) a k) χ-(e+1)
  have hχk:χ≤k:=(wider (A) b k).trans (before (A) b k)
  have mχ:m+(e+1)≤χ:=side1
  have mk:m<k:=by omega
  filter_upwards [eventually_ge_atTop k,WilsonThermometerWeakWardClearance.original R d radius k (by omega)] with N hk ward
  refine ⟨hk,?_⟩
  intro p hχ T₀ z q close w pivot
  let dates:Fin 2→ℕ:=![k,χ]
  have live(i:Fin 2):dates i≤N:=by fin_cases i;exact hk;exact hχ
  have deep(i:Fin 2):m+e+1≤dates i:=by
    fin_cases i
    · change m+e+1≤k;omega
    · change m+e+1≤χ;omega
  obtain ⟨far,period⟩:=layout m p income q close
  obtain ⟨t,c₀,c₁,apart,left,right⟩:=housing k m N p hk dates deep live z q far period
  refine ⟨m,mk.le,t,c₀,c₁,apart,left,?_⟩
  intro r v
  refine ⟨ward p m mk hk z q far period t r v,?_⟩
  intro a inside price
  exact WilsonThermometerWeakSameRunCross.moved R r hk hχ (by omega:m≤χ) c₁ (w 1+t) pivot v a inside price right

end YM.Integration.WilsonThermometerWeakWardChambers
end
