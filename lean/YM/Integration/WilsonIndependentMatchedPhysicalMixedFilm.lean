import YM.Integration.WilsonIndependentMatchedPhysicalAxes
import YM.Integration.WilsonIndependentFittedRosterProducts
import YM.Integration.WilsonIndependentFittedRosterCash
/-! The true fixed-pivot expansion of each mixed scalar on the dated heterogeneous physical course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalMixedFilm
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterSlots (entry wallet degree count)
open WilsonIndependentMatchedPhysicalComponent (volume price)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalMasks (ranksV)
variable {G:Gauge}{n k e u₀:ℕ}{H:Hol G}{Q:Fin (n+1)→SealR G}{v:∀i,Rails (Q i).h k u₀ e}
local notation "C" => Credit.leanC
abbrev Courts:=(i:Fin (n+1))→CutsP H (Q i).ans (Q i).path (v i) C C C C

open WilsonIndependentMatchedPhysicalSector (stamp field)
open WilsonIndependentFittedRosterFilms (Vote piece factor)
open WilsonIndependentFittedReportedFilm (funded)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentFittedRosterCash (roster numerical reserve)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonPhysicalMarkedDefect.RawBank (cash)

def senior (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(flag:Fin (n+1)→Bool)
    (host K N:ℕ)(F:Wilt Q)(y:ℝ)(o:CellR){r:ℕ}(x:Fin r→YForest G):Cost:=
  reading (cruises V.draws V.paid N (ranksV flag k fun s=>(Q s).h) K host (field flag X F y o)).2 x

def lane (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(flag:Fin (n+1)→Bool)
    (host m N:ℕ)(s:Fin (n+1))(q:Vote (Q s).F (flag s)):Cost:=
  clock V.draws V.paid N m host (factor (dose (X s) 1) (flag s) q)

def naked (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(flag:Fin (n+1)→Bool)
    (host K N:ℕ)(F:Wilt Q)(y:ℝ)(o:CellR){r:ℕ}(x:Fin r→YForest G)(sel:∀s,Vote (Q s).F (flag s)):Cost:=
  reading (cruises V.draws V.paid N (ranksV flag k fun s=>(Q s).h) K host
    (WilsonIndependentMatchedPhysicalAxes.field flag X F y o sel)).2 x

open private kept from YM.Integration.WilsonIndependentFittedRosterProducts

theorem original (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(flag:Fin (n+1)→Bool)
    (host m K N:ℕ)(F:Wilt Q)(y:ℝ)(o:CellR){r:ℕ}(x:Fin r→YForest G)(filed:stamp V X m K N)
    (older:host ≤ m)(start:m ≤ K)(live:K ≤ N):
    senior V X flag host K N F y o x=roster (lane V X flag host m N) (naked V X flag host K N F y o x):=by
  let I:=fun s=>Vote (Q s).F (flag s)
  let d:=fun s=>dose (X s) 1
  let P:=(fun s=>piece true (X s) 1 (d s) (F s) y o (flag s))
  let Q':=(fun s=>piece false (X s) 1 0 (F s) y o (flag s))
  have age s:(X s).i=K-m:=by
    have top:(X s).m+(X s).i=K:=(filed s).2.2.2.1
    rw [(filed s).2.2.1] at top
    omega
  have affix (s:Fin (n+1))(q:I s):P s q=
      funded (reel (relativeC V.draws V.paid N m (K-m)) (factor (d s) (flag s) q)) (Q' s q):=by
    have got:=WilsonIndependentFittedRosterFilms.scaled (X s) 1 (d s) (F s) y o (flag s) q
    rw [kept,(filed s).1,(filed s).2.1,(filed s).2.2.2.2,(filed s).2.2.1,age s] at got
    exact got
  have whole:=WilsonIndependentFittedProductCensus.stopped V.draws V.paid V.hG V.green N m (K-m) host older
    (by rwa [Nat.add_sub_of_le start]) n (fun j=>degree (flag j) k (Q j).h) I
    (fun s=>factor (d s) (flag s)) P Q'
    (fun j z=>WilsonIndependentFittedRosterFilms.authenticated (X j) 1 (d j) (F j) y o true (flag j) z)
    (fun j z=>WilsonIndependentFittedRosterFilms.authenticated (X j) 1 0 (F j) y o false (flag j) z)
    affix r x
  have inlet:field flag X F y o=MassP G ℝ n (fun j=>∑z,P j z):=by
    apply congrArg (MassP G ℝ n)
    funext j
    exact WilsonIndependentFittedRosterFilms.entire ..
  rw [Nat.add_sub_of_le start] at whole
  unfold senior
  rw [inlet]
  unfold ranksV
  rw [whole]
  unfold roster
  apply Finset.sum_congr (by ext w; simp)
  intro w _
  rfl

theorem charged (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(flag:Fin (n+1)→Bool)
    (host m K N:ℕ)(F:Wilt Q)(y:ℝ)(o:CellR)(x:Fin 0→YForest G)(filed:stamp V X m K N)
    (older:host ≤ m)(start:m ≤ K)(live:K ≤ N)(q:ℕ)(depth:q≤e)(g:ℝ)(small:|g|≤1)(u:ℕ)(M:ℝ)
    (heard:∀sel,response e u (cruises V.draws V.paid N (ranksV flag k fun s=>(Q s).h) K host
      (WilsonIndependentMatchedPhysicalAxes.field flag X F y o sel)) M):
    let A:=lane V X flag host m N
    ‖cash q g (embed (senior V X flag host K N F y o x))‖≤
      (numerical q g A+(((n+1:ℕ):ℝ)+1)*|g|^(q+1)*reserve q A)*(((q+1:ℕ):ℝ)*M):=by
  intro A
  rw [original V X flag host m K N F y o x filed older start live]
  have paid:=WilsonIndependentFittedRosterCash.original q g small A (naked V X flag host K N F y o x)
    (((q+1:ℕ):ℝ)*M)
  simp only [Fintype.card_fin] at paid
  apply paid
  intro w
  calc
    _ ≤ ∑_j∈Finset.range (q+1),M:=by
      apply Finset.sum_le_sum
      intro j hj
      have tier:=(heard w).2 j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans depth) x
      simp only [naked,embed,coeff_map,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
      simpa using tier
    _ = _:=by simp

end YM.Integration.WilsonIndependentMatchedPhysicalMixedFilm
