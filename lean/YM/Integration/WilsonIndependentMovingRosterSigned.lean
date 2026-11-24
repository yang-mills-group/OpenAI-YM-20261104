import YM.Integration.WilsonIndependentMovingRosterRejoin
import YM.Integration.WilsonSeparatedPrefixMovingTriangle

/-! The complete earlier scalar has one unformed exterior contact and
one triangular family of first exterior contacts with already formed near deposits. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMovingRosterSigned
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingUnformedSector (fresh)
open WilsonIndependentMovingRosterRejoin (crossed)
open WilsonIndependentMovingRosterCut (residual contribution)
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(live:R.anchor ≤ t)
    (start:t ≤ m)(ear:older ≤ m)(top:m ≤ N):
    (residual R Q F φ ψ X Y o y t m older N).2 q 0 ω=
      (∑d∈range (N-m),fresh R Q F φ ψ X Y o y t m older N q ω (m+d))+
      ∑d∈range (N-m),∑j∈(range (N-m)).filter (fun j=>d ≤ j),
        crossed R Q F φ ψ X Y o y t m older N q ω (m+d) (m+j):=by
  rw [WilsonIndependentMovingRosterCut.original R Q F roster far φ ψ X Y o y t m older N live start ear top]
  simp only [Prod.snd_sum,Finset.sum_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have fine:=Finset.mem_range.mp hd
  rw [WilsonIndependentMovingRosterRejoin.original R Q F roster far φ ψ X Y o y t m older (m+d) N q ω
    live start (by omega) (by omega) (by omega)]
  congr 1
  have move:=WilsonSeparatedPrefixMovingTriangle.row N m d fine
    (fun j=>crossed R Q F φ ψ X Y o y t m older N q ω (m+d) (m+j)) (by simp [WilsonIndependentMovingRosterRejoin.crossed])
  simpa only [Nat.add_assoc,Nat.add_comm 1 d,Nat.add_left_comm] using move

end YM.Integration.WilsonIndependentMovingRosterSigned
