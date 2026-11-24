import YM.Integration.WilsonIndependentMovingRosterTopSplit
import YM.Integration.WilsonIndependentMovingRosterCut

/-! The uncorrected term of the submitted finite cuts is the earlier
product used by the moving first-connection theorem. The far field keeps
its own reporting date and the genuine rescaled center. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterTopAtHomes

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterMasks (choose quiet placed)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMovingRosterTopFields (offered stable fitted)
open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonIndependentMovingRosterCut (parcel residual)
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}{n e k h:ℕ}{d D u:Fin ((n+1)+1)→ℕ}
    {F:(s:Fin ((n+1)+1))→Labels.Frame G (d s)}{T:(s:Fin ((n+1)+1))→SectionData (F s)}
    {p:∀s,d s<D s}{v:(s:Fin ((n+1)+1))→Rails (d s) k (u s) e}{E W K U:Credit}
    (R:Realm G (e+1) E)(X:(s:Fin ((n+1)+1))→CutsP H (T s) (p s) (v s) E W K U)
local notation "Qₙ" => (fun i:Fin (n+1)=>sectionSeal (T (Fin.succ i)) (p (Fin.succ i)))
local notation "Q₀" => sectionSeal (T 0) (p 0)
local notation "Vₙ" a:max => (fun i:Fin (n+1)=>dose (X (Fin.succ i)) (a (Fin.succ i)))
local notation "V₀" a:max => dose (X 0) (a 0)
local notation "near" φ:max => (fun i:Fin (n+1)=>φ (Fin.succ i))
local notation "centers" y:max m:max t:max => (Fin.cons (y/paceT R.draws.S m t) (fun _:Fin (n+1)=>y))

theorem sources {t m N:ℕ}(coarse:(X 0).m=t)(regular:∀s:Fin (n+1),(X s.succ).m=m)
    (a:Fin ((n+1)+1)→ℝ)(φ:(i:Fin ((n+1)+1))→Rarity (D i))(y:ℝ)(o:CellR):
    MassP G ℝ (n+1) (fitted R X a φ (centers y m t) (fun _=>o) N)=
      agateV (current R Q₀ (φ 0) (V₀ a) t N N (y/paceT R.draws.S m t) o)
        (Ashore Qₙ R.draws R.paid (near φ) (Vₙ a) m N N y o):=by
  let B:=fitted R X a φ (centers y m t) (fun _=>o) N
  have atFar:B 0=current R Q₀ (φ 0) (V₀ a) t N N (y/paceT R.draws.S m t) o:=by
    dsimp only [B,fitted,Fin.cons_zero,current]
    rw [coarse]
    rfl
  have atNear:Fin.tail B=awaken Qₙ R.draws R.paid (near φ) (Vₙ a) m N N y o:=by
    funext i
    dsimp only [B,Fin.tail,fitted,Fin.cons_succ,awaken,arouse]
    rw [regular]
    rfl
  exact congrArg₂ agateV atFar (congrArg (MassP G ℝ n) atNear)

theorem original {older t m N:ℕ}(before:older≤N)(degrees:∀i,d i≤h)(cap:h≤k)
    (same:∀i,(X i).vesselsC=R)(last:∀i,(X i).N=N)(upper:∀i,(X i).m+(X i).i=N)
    (coarse:(X 0).m=t)(regular:∀s:Fin (n+1),(X s.succ).m=m)
    (a:Fin ((n+1)+1)→ℝ)(φ:(i:Fin ((n+1)+1))→Rarity (D i))(y:ℝ)(o:CellR):
    let c:=centers y m t
    let P:=stable X a φ c (fun _=>o)
    let B:=fitted R X a φ c (fun _=>o) N
    let size:=d 0+capP Qₙ
    let law:=fun j=>cruises R.draws R.paid N j N older
    law ((n+2)*k) (MassP G ℝ (n+1) (offered X a φ c (fun _=>o)))-
      cruises R.draws R.paid N size m older (agateV (current R Q₀ (φ 0) (V₀ a) t m N (y/paceT R.draws.S m t) o)
        (parcel R Qₙ (near φ) (Vₙ a) o y m m N))=
      residual R Qₙ Q₀ (near φ) (φ 0) (Vₙ a) (V₀ a) o y t m older N+
      ∑j∈Finset.univ.erase (quiet (n+1)),law (ranks (choose (n+1) j) k h) (placed P B j):=by
  intro c P B size law
  have split:=WilsonIndependentMovingRosterTopSplit.original R X before degrees cap same last upper a φ c (fun _=>o)
  have grade:=WilsonIndependentMovingRosterTopFields.grades R X same last upper a φ c (fun _=>o)
  have background:Auth size (MassP G ℝ (n+1) B):=
    (grade 0).2.manor (manCo (Fin.tail B) (fun i=>d i.succ) (fun i=>(grade i.succ).2))
  have less:capP Qₙ≤(n+1)*k:=by
    simpa only [capP,asp,sectionSeal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] using
      (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _:Fin (n+1)=>k) (fun i _=>(degrees i.succ).trans cap))
  have fits:size≤(n+2)*k:=by
    have d₀: d 0≤k:=(degrees 0).trans cap
    change d 0+capP Qₙ≤(n+1+1)*k
    rw [Nat.succ_mul]
    omega
  have small:=WilsonIndependentMatchedCoverGrade.carried R.draws R.paid R.hG R.green before le_rfl
    (MassP G ℝ (n+1) B) background fits
  have born:=sources R X (N:=N) coarse regular a φ y o
  unfold WilsonIndependentMovingRosterCut.residual
  dsimp only
  rw [←born]
  change _-_= (law size (MassP G ℝ (n+1) B)-_)+_
  change law size (MassP G ℝ (n+1) B)=law ((n+2)*k) (MassP G ℝ (n+1) B) at small
  change law ((n+2)*k) _-law ((n+2)*k) (MassP G ℝ (n+1) B)=_ at split
  rw [small,←split]
  abel

end YM.Integration.WilsonIndependentMovingRosterTopAtHomes
