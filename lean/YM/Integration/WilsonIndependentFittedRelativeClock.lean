import YM.Integration.WilsonOlderFreshSoftSocketKinetic
import YM.Integration.WilsonIndependentMatchedReportedProxy

/-! The clock of the actual held-field return cancels precisely the inverse
clock used by the reported position column, coefficient by coefficient. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRelativeClock
open Function Finset Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOlderFreshSoftSocketKinetic (reading)
open scoped Classical BigOperators
variable {G:Gauge}

theorem reported (A:Levels G)(O:ChartRatio G)(N m i:ℕ)(c:Cost):
    clock A O N (m+i) m c = reel (relativeF A O N m i) c :=by
  induction i generalizing c with
  | zero=>simp [clock,relativeF,palmB]
  | succ i ih=>
    rw [← WilsonOlderFreshSoftSocketKinetic.combine A O N (m+i.succ) (m+i) m
      (Nat.le_add_right ..) (by omega) c]
    have step:clock A O N (m+i.succ) (m+i) c=reel (ratioHigh A O N (m+i)) c:=by
      rw [clock,dif_pos (by omega),clock,dif_neg (by omega)]
    rw [step,ih]
    change ((reel (relativeF A O N m i)).comp (reel (ratioHigh A O N (m+i)))) c=_
    rw [reel_chart]
    rfl

theorem restored (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N m i:ℕ)(top:m+i≤N)(c:Cost):
    clock A O N (m+i) m (reel (relativeC A O N m i) c)=c:=by
  rw [reported]
  change ((reel (relativeF A O N m i)).comp (reel (relativeC A O N m i))) c=c
  rw [reel_chart,(direction simple localO top).2,reel_one]

theorem original (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N m i k:ℕ)(top:m+i≤N)(P Q:Era G ℝ)(c:Cost)(high:Auth k P)(low:Auth k Q)
    (filed:∀n,P.1 n=affix (reel (relativeC A O N m i) c) (Q.1 n))
    {r:ℕ}(v:Fin r → YForest G):
    reading (cruises A O N k (m+i) m P).2 v=
      c*reading (cruises A O N k (m+i) m Q).2 v:=by
  have paid:=WilsonOlderFreshSoftSocketHistory.original A O simple localO N k (m+i) m
    (Nat.le_add_right ..) top P Q (reel (relativeC A O N m i) c) high low filed
  rw [paid,restored A O simple localO N m i top,WilsonOlderFreshSoftSocketKinetic.valued]

end YM.Integration.WilsonIndependentFittedRelativeClock
