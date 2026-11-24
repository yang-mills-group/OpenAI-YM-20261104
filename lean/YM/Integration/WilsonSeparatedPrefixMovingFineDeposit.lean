import YM.Integration.WilsonSeparatedPrefixMovingFineFare
import YM.Integration.WilsonSeparatedPrefixMovingLenses
import YM.WilsonCoeffUV.Product.Report.Motif

/-! Fine-side first contact of the exterior with two or more separately
located normalized inputs. Each input and its test use their own filed date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingFineDeposit
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}{k e u a n:ℕ}{E W V L:Credit}

theorem original (R:Realm G (e+1) E)(spring:SpringD R k u a W)(Q:Fin (n+1)→SealR G)
    (Qe:SealR G)(home:HorizonP H R W V Q)(outer:PassportC H R Qe W V)(i N t m:ℕ)
    (beginAt:R.anchor≤t)(coarse:t≤m)(fine:m ≤ i)(edge:i<N)
    (target left extra:ℕ)(wave:a=(∑j,(Q j).h)+Qe.h+extra)(decay:a=u+Qe.h+target+left)
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
    let wages j:=WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=b)
      (Q j) (X j) (φ j) Z x y (B j)
    let exterior:=WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=b)
      Qe w ψ Z (x/τ) (y/τ) Be
    (∀j,∀p∈tsupport (φ j).ψ.val,∀q∈tsupport ψ.ψ.val,τ*gap ≤ dist p (τ • q)) →
    (∀j,radiusH (φ j) η y≤radius) → radiusH ψ (η/τ) (y/τ)≤radius →
    (∀j,(VisitsT (φ j) x y o).Nonempty) → (VisitsT ψ (x/τ) (y/τ) o).Nonempty →
    verseI A R.paid i N (Qe.h+l) (agateV far inner)=
      born+agateV (verseI A R.paid i N Qe.h far) (verseI A R.paid i N l inner) ∧
    Auth (Qe.h+l) born ∧ Flush e u η born
      (R.cash (priceWG G e k u a E W) i*
        (((τ^target)⁻¹*(τ^left)⁻¹*x^extra*((16*radius)^u*((P.L.val:ℝ)/gap)^a))*
          (exterior*((coinMat k e)^n*∏j,wages j)))):=by
  intro A P τ x η near far inner l born b wages exterior separate nearBox farBox nearLive farLive
  have sold:=WilsonSeparatedPrefixMovingUnformed.original R spring Q Qe home outer i N t m beginAt
    coarse fine edge seat φ ψ X w y (τ*gap) radius Z B Be o clock view (mul_pos (pace_pos ..) positive)
    nearPrice farPrice separate nearBox farBox nearLive farLive
  refine ⟨sold.1,sold.2.1,?_⟩
  have zoom:1≤τ:=pace_ge _ coarse
  have radiusPos:0≤radius:=(zero_le_one.trans (fieldCap (φ 0) η y)).trans (nearBox 0)
  have dom:radius≤τ*radius:=(le_mul_of_one_le_left radiusPos zoom)
  obtain ⟨_,_,fee⟩:=sold
  change Flush e u η born (R.cash (priceWG G e k u a E W) i *
    (pearlB u a (4*max radius (τ*radius)) (τ*gap/η)*
       (WilsonSeparatedPrefixMovingUnformed.fare H E W V Qe w ψ e b Z (x/τ) (y/τ) Be*
       nuP (coinMat k e) n (fun j=>WilsonSeparatedPrefixMovingUnformed.fare H E W V
          (Q j) (X j) (φ j) e b Z x y (B j))))) at fee
  have outerCost:WilsonSeparatedPrefixMovingUnformed.fare H E W V Qe w ψ e b Z (x/τ) (y/τ) Be=
      ((x/τ)^Qe.h)⁻¹*exterior:=WilsonSeparatedPrefixMovingOwnDate.units ..
  rw [max_eq_right dom,outerCost,WilsonSeparatedPrefixMovingFineFare.roster] at fee
  have price:=WilsonSeparatedPrefixMovingFineFare.powers u a l Qe.h target left extra wave decay
    x (P.L.val:ℝ) τ gap radius (pace_pos ..) (by exact_mod_cast P.L.pos) (pace_pos ..) positive
  let pref:=pearlB u a (4*(τ*radius)) (τ*gap/η)
  let innerFee:=(coinMat k e)^n * ∏j,wages j
  change Flush e u η born (_*(pref*((((x/τ)^Qe.h)⁻¹*exterior)*((x^l)⁻¹*innerFee)))) at fee
  have times:pref*((((x/τ)^Qe.h)⁻¹*exterior)*((x^l)⁻¹*innerFee))=
      (pref*(((x/τ)^Qe.h)⁻¹*(x^l)⁻¹))*(exterior*innerFee):=by ring
  change pref*(((x/τ)^Qe.h)⁻¹*(x^l)⁻¹)=_ at price
  rw [times,price] at fee
  exact fee

end YM.Integration.WilsonSeparatedPrefixMovingFineDeposit
