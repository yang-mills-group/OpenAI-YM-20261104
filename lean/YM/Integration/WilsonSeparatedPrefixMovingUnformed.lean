import YM.Integration.WilsonSeparatedPrefixMovingOwnDate
import YM.Integration.WilsonSeparatedPrefixMovingLenses
import YM.WilsonCoeffUV.Product.Report.Motif

/-! Fine-side first contact of the exterior with two or more separately
located normalized inputs. Each input and its test use their own filed date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingUnformed
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}{k e u a n:ℕ}{E W V L:Credit}

/-- The common fine address is expressed in both native rulers. -/
theorem rulers (S:Schedule)(t m i:ℕ): paceT S t i=paceT S m i/paceT S m t:=by
  unfold paceT; field_simp [(S.a_pos t).ne',(S.a_pos m).ne']

def fare (H:Hol G)(E W V:Credit)(Q:SealR G)(X:Q.Rider)(φ:Rarity Q.D)(e u:ℕ)
    (Z x y B:ℝ):ℝ:=let α:=(polarBill H Q.ans Q.path e u E W V).choose
  charge φ u Q.h x y (α.buy Z*WilsonSeparatedPrefixMovingOwnDate.fee Q e X) B

theorem original (R:Realm G (e+1) E)(spring:SpringD R k u a W)(Q:Fin (n+1)→SealR G)
    (Qe:SealR G)(home:HorizonP H R W V Q)(outer:PassportC H R Qe W V)(i N t m:ℕ)
    (beginAt:R.anchor≤t)(coarse:t≤m)(fine:m ≤ i)(edge:i<N)
    (seat:Qe.h+(∑j,(Q j).h)≤k)(φ:Wilt Q)(ψ:Rarity Qe.D)(X:Herit Q)(w:Qe.Rider)
    (y gap radius Z:ℝ)(B:Fin (n+1)→ℝ)(Be:ℝ)(o:CellR)
    (clock:Compar R.draws.S R.y m (i+1)≤Z)(view:Compar R.draws.S R.y t (i+1)≤Z)
    (positive:0<gap)(nearPrice:∀j,Amplitude (φ j) (B j))(farPrice:Amplitude ψ Be):
    let A:=R.draws
    let P:=ll A i
    let τ:=paceT A.S m t
    let x:=paceT A.S m (i+1)
    let η:=x*P.L.val
    let near j:=locale o ((Q j).spins A R.paid (φ j) m (i+1) N y (X j))
    let far:=locale o (Qe.spins A R.paid ψ t (i+1) N (y/τ) w)
    let inner:=MassP G ℝ n near
    let l:=∑j,(Q j).h
    let born:=JoinGap A R.paid i N Qe.h l far inner
    let b:=u+a
    let wages j:=fare H E W V (Q j) (X j) (φ j) e b Z x y (B j)
    let exterior:=fare H E W V Qe w ψ e b Z (x/τ) (y/τ) Be
    (∀j,∀p∈tsupport (φ j).ψ.val,∀q∈tsupport ψ.ψ.val,gap ≤ dist p (τ • q)) →
    (∀j,radiusH (φ j) η y≤radius) → radiusH ψ (η/τ) (y/τ)≤radius →
    (∀j,(VisitsT (φ j) x y o).Nonempty) → (VisitsT ψ (x/τ) (y/τ) o).Nonempty →
    verseI A R.paid i N (Qe.h+l) (agateV far inner)=
      born+agateV (verseI A R.paid i N Qe.h far) (verseI A R.paid i N l inner) ∧
    Auth (Qe.h+l) born ∧ Flush e u η born
      (R.cash (priceWG G e k u a E W) i*
        (pearlB u a (4*max radius (τ*radius)) (gap/η)*(exterior*nuP (coinMat k e) n wages))):=by
  intro A P τ x η near far inner l born b wages exterior separate nearBox farBox nearLive farLive
  have zoom:1≤τ:=pace_ge _ coarse
  have xi:0<x:=pace_pos ..
  have bound:η≤1:=by change paceT A.S m (i+1)*(A.S.block i).val≤1;rw [pace_step];exact pace_le _ fine
  have reach:η/τ=x/τ*P.L.val:=by dsimp only [η];ring
  have farIncome:=WilsonSeparatedPrefixMovingOwnDate.column outer t (i+1) N b beginAt
    (coarse.trans (fine.trans (Nat.le_succ _))) edge Z view w ψ (y/τ) o P Be farPrice
  rw [rulers A.S t m (i+1)] at farIncome
  have ni j:=WilsonSeparatedPrefixMovingOwnDate.column (home j).some m (i+1) N b
    (beginAt.trans coarse) (fine.trans (Nat.le_succ _)) edge Z clock (X j) (φ j) y o P (B j) (nearPrice j)
  let front:=saddleP P.L (VisitsT ψ (x/τ) (y/τ) o)
  let roots j:=saddleP P.L (VisitsT (φ j) x y o)
  have apart j:SplitHill front (roots j) η (4*max radius (τ*radius)) (gap/η):=
    WilsonSeparatedPrefixMovingLenses.original P (φ j) ψ x y τ gap radius radius o xi zoom bound
      positive (separate j) (nearBox j) (reach ▸ farBox) (nearLive j) farLive
  exact WilsonSeparatedPrefixMovingCohorts.crossing R spring (beginAt.trans (coarse.trans fine)) edge
    le_rfl far near (fun j=>(Q j).h) seat front roots η (4*max radius (τ*radius)) (gap/η)
    exterior wages apart farIncome ni

end YM.Integration.WilsonSeparatedPrefixMovingUnformed
