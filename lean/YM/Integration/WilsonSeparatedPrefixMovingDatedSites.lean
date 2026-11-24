import YM.Integration.WilsonSeparatedPrefixMovingPinController
import YM.Integration.WilsonSeparatedPrefixMovingPinDay
import YM.Integration.WilsonSeparatedPrefixMovingUnformedSector
import YM.Integration.WilsonSeparatedPrefixMovingPinHearing
import YM.Integration.WilsonIndependentMatchedVacant

/-! Restrict a dated crossing census on its own receiver. Every retained cohort keeps its original pin. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingDatedSites
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open Finset
open scoped BigOperators Topology Classical

open WilsonPositionProgramPinnedHearthHistory (pin)
variable {G:Gauge}{e:ℕ}{E:Credit}


open WilsonSeparatedPrefixMovingPinController (Sites collected)
open WilsonCoeffUV.Wheel.Mark
open scoped BigOperators

def select {u:ℕ}(canvas:Sites G e u)(K:ℕ):Sites G e u where
  part:=fun i=>if K ≤ i then canvas.part i else 0
  authentic:=by
    intro i k X auth
    split
    · exact canvas.authentic i k X auth
    · exact unstamped
  income:=by
    intro i X η A paid
    split
    · exact canvas.income i X η A paid
    · exact ⟨paid.1,fun _ _ _ _=>Award.zero.more paid.1⟩

theorem nil (R:Realm G (e+1) E)(k N i older:ℕ)(lo:older ≤ i)(hi:i ≤ N):
    cruises R.draws R.paid N k i older (0:Era G ℝ)=0:=by
  induction lo using Nat.decreasingInduction with
  | self=>rw [cruises_top]
  | of_succ j hj ih=>rw [cruises_sub _ _ _ _ _ hj,ih,verseZero R.draws (hj.trans_le hi) R.hG R.green]

theorem earned {u:ℕ}(R:Realm G (e+1) E)(canvas:Sites G e u)(K k N i older:ℕ)(X:Era G ℝ)(lo:older ≤ i)(hi:i ≤ N):
    collected R (select canvas K) k N i older X=if K ≤ i then collected R canvas k N i older X else 0:=by
  by_cases paid:K ≤ i
  · simp only [collected,select,if_pos paid]
  · simp only [collected,select,if_neg paid,AddMonoidHom.zero_apply]
    exact nil R k N i older lo hi

theorem fresh {n u:ℕ}(R:Realm G (e+1) E)(canvas:Sites G e u)(K:ℕ)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)
    (i:ℕ)(lo:older ≤ i)(hi:i ≤ N):
    WilsonSeparatedPrefixMovingUnformedSector.mountedRow R (select canvas K) Q F φ ψ X Y o y t m older N q ω i=
      if K ≤ i then WilsonSeparatedPrefixMovingUnformedSector.mountedRow R canvas Q F φ ψ X Y o y t m older N q ω i else 0:=by
  dsimp only [WilsonSeparatedPrefixMovingUnformedSector.mountedRow]
  rw [earned R canvas K _ N i older _ lo hi]
  split <;> rfl

theorem crossed {n u:ℕ}(R:Realm G (e+1) E)(canvas:Sites G e u)(K:ℕ)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)
    (i j:ℕ)(lo:older ≤ i)(hi:i ≤ N):
    WilsonSeparatedPrefixMovingPinDay.crossed R (select canvas K) Q F φ ψ X Y o y t m older N q ω i j=
      if K ≤ i then WilsonSeparatedPrefixMovingPinDay.crossed R canvas Q F φ ψ X Y o y t m older N q ω i j else 0:=by
  unfold WilsonSeparatedPrefixMovingPinDay.crossed
  by_cases lived:i < j
  · simp only [if_pos lived]
    rw [earned R canvas K _ N i older _ lo hi]
    split <;> rfl
  · simp only [if_neg lived,ite_self]

theorem original (f:ℕ→ℝ)(m K N:ℕ)(hm:m ≤ K)(hk:K ≤ N):
    ∑i∈Finset.range (N-m),(if K ≤ m+i then f (m+i) else 0)=∑i∈Finset.range (N-K),f (K+i):=by
  have len:(K-m)+(N-K)=N-m:=by omega
  rw [←len,Finset.sum_range_add]
  have gone:(∑i∈Finset.range (K-m),(if K ≤ m+i then f (m+i) else 0))=0:=by
    apply Finset.sum_eq_zero
    intro i hi
    have less:=Finset.mem_range.mp hi
    exact if_neg (by omega)
  rw [gone,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have key:m+((K-m)+i)=K+i:=by omega
  rw [key,if_pos (Nat.le_add_right K i)]

end YM.Integration.WilsonSeparatedPrefixMovingDatedSites
