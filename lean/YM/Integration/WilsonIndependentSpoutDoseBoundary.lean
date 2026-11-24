import YM.Integration.WilsonIndependentSpoutScalarLedger
import YM.Integration.WilsonIndependentFittedRelativeClock

/-! A filed thermal dose passes through the actual N-conditioned normalized transfer and its original reporting clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentSpoutDoseBoundary
open Function Finset PowerSeries Lattice Wilson RG Precision Source Labels WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Power WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos PertExtension
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentSpoutScalarLedger (ground)
open scoped BigOperators Classical
variable {G:Gauge}(A:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)

def into (N m:ℕ):Cost →+* Cost:=reel (relativeC A O N m (N-m))
def measure (N k b m:ℕ)(P:Era G ℝ):Cost:=into A O N m (ground (cruises A O N k b m P))

include simple ratio
theorem restored (N m:ℕ)(hm:m ≤ N)(c:Cost):
    clock A O N N m (into A O N m c)=c:=by
  have z:=WilsonIndependentFittedRelativeClock.restored A O simple ratio N m (N-m) (by omega) c
  rwa [show m+(N-m)=N by omega] at z

theorem inverse (N m:ℕ)(hm:m ≤ N)(c:Cost):
    into A O N m (clock A O N N m c)=c:=by
  have z:=WilsonIndependentFittedRelativeClock.reported A O N m (N-m) c
  rw [show m+(N-m)=N by omega] at z
  rw [z]
  change ((reel (relativeC A O N m (N-m))).comp (reel (relativeF A O N m (N-m)))) c=c
  rw [reel_chart,(direction simple ratio (by omega:m+(N-m) ≤ N)).1,reel_one]

theorem earned (N k b m:ℕ)(mb:m ≤ b)(bn:b ≤ N)(P Q:Era G ℝ)(c:Cost)
    (real:Auth k P)(base:Auth k Q)(filed:∀n,P.1 n=affix c (Q.1 n)):
    measure A O N k b m P=into A O N b c * measure A O N k b m Q:=by
  have combined:=WilsonOlderFreshSoftSocketHistory.original A O simple ratio N k b m mb bn P Q c real base filed
  unfold measure ground
  rw [combined,WilsonOlderFreshSoftSocketKinetic.valued,map_mul]
  have inject:=restored A O simple ratio N b bn c
  have timeline:=WilsonOlderFreshSoftSocketKinetic.combine A O N N b m mb bn (into A O N b c)
  rw [inject] at timeline
  rw [timeline,inverse A O simple ratio N m (mb.trans bn)]

theorem cap (N b m h k:ℕ)(mb:m ≤ b)(bn:b ≤ N)(hk:h ≤ k)(Q:Era G ℝ)(paid:Auth h Q):
    cruises A O N h b m Q=cruises A O N k b m Q:=by
  induction mb using Nat.decreasingInduction with
  | self=>rw [cruises_top,cruises_top]
  | of_succ i hi ih=>
    rw [cruises_sub A O N h Q hi,cruises_sub A O N k Q hi,←ih]
    exact verseExpand A (hi.trans_le bn) simple ratio (cruising A simple ratio hi bn paid) hk

theorem checkedSum {T:Type}[Fintype T](N b m k:ℕ)(mb:m ≤ b)(bn:b ≤ N)(Q:T → Era G ℝ)(paid:∀t,Auth k (Q t)):
    cruises A O N k b m (∑t,Q t)=∑t,cruises A O N k b m (Q t):=by
  induction mb using Nat.decreasingInduction with
  | self=>simp only [cruises_top]
  | of_succ i hi ih=>
    rw [cruises_sub A O N k (∑t,Q t) hi,ih]
    have add:=verse_sum A simple (hi.trans_le bn) ratio (S:=univ)
      (fun t _=>cruising A simple ratio hi bn (paid t)) (fun _=>1)
    simp only [one_smul] at add
    rw [add]
    exact Finset.sum_congr rfl fun t _=>(cruises_sub A O N k (Q t) hi).symm

end YM.Integration.WilsonIndependentSpoutDoseBoundary
