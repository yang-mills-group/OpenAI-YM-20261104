import YM.Integration.WilsonOlderFreshSoftSocketVerseHistory
import YM.Integration.WilsonIndependentMatchedCoverProfile
import YM.Integration.WilsonIndependentMatchedRosterMasks

/-! The complete ordinary product of signed marked inputs at a common original cutoff. -/
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketVerseProduct
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel.Flooring
open PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedCoverProfile (Income)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet placed)
open scoped Classical BigOperators
variable {G:Gauge}

def Paid (k e:ℕ)(P:Era G ℝ)(A:ℝ):Prop:=Auth k P ∧ 0 ≤ A ∧ Saturation e 0 0 P.2 0 A

private theorem earn {k e:ℕ}{P:Era G ℝ}{A:ℝ}(paid:Paid k e P A):
    Income P k e 0 (fun _=>0) A:=by
  refine ⟨paid.1,?_⟩
  intro δ hd j r hj
  have src:=YieldP.same (paid.2.2 j hj r (Nat.zero_le _)) hd
  exact ⟨by simpa only [Mer.Rent,Fruit,Award,quoteT,hedge,autumn,pow_zero] using src.wax,
    by simpa only [Mer.Rent,Fruit,Award,quoteT,hedge,autumn,pow_zero] using src.wane,
    by simpa only [Mer.Rent,Fruit,Award,quoteT,hedge,autumn,pow_zero] using src.toll⟩

theorem collect {k e:ℕ}{P:Era G ℝ}{p:ProfileW}{A:ℝ}(inc:Income P k e 0 p A):Paid k e P A:=by
  have each (j:ℕ)(hj:j≤e)(r:ℕ):Fruit 0 0 0 (P.2 j r) A:=by
    simpa only [Mer.Rent,Fruit,Award,quoteT,hedge,autumn,pow_zero] using (inc.2 0 le_rfl j r hj).paid
  have bound:=each 0 (Nat.zero_le _) 0
  exact ⟨inc.1,le_trans (tsum_nonneg bound.1) bound.2.2,fun j hj r _=>each j hj r⟩

theorem pair {k l e:ℕ}{P Q:Era G ℝ}{A B:ℝ}(left:Paid k e P A)(right:Paid l e Q B):
    Paid (k+l) e (agateV P Q) (coinMat (k+l) e*A*B):=by
  have sold:=WilsonIndependentMatchedCoverProfile.occupied (earn left) (earn right)
  refine ⟨sold.1,mul_nonneg (mul_nonneg (by unfold coinMat;positivity) left.2.1) right.2.1,?_⟩
  intro j hj r _
  have permit:=(sold.2 0 le_rfl j r hj).paid
  simpa only [Mer.Rent,Fruit,Award,quoteT,hedge,autumn,pow_zero] using permit

def cost (e:ℕ):{n:ℕ}→(Fin (n+1)→ℕ)→(Fin (n+1)→ℝ)→ℝ
  | 0, _, A => A 0
  | Nat.succ _, d, A => coinMat (∑i,d i) e*A 0*cost e (d ∘ Fin.succ) (A ∘ Fin.succ)

theorem original {e n:ℕ}(d:Fin (n+1)→ℕ)(P:Fin (n+1)→Era G ℝ)(A:Fin (n+1)→ℝ)
    (hired:∀i,Paid (d i) e (P i) (A i)):Paid (∑i,d i) e (MassP G ℝ n P) (cost e d A):=by
  induction n with
  | zero=>simpa [MassP,cost] using hired 0
  | succ n ih=>
    have tail:=ih (d ∘ Fin.succ) (P ∘ Fin.succ) (A ∘ Fin.succ) (fun i=>hired i.succ)
    rw [cost,Fin.sum_univ_succ d]
    exact pair (hired 0) tail

theorem signed {e n:ℕ}(d:Fin (n+1)→ℕ)(P Q:Fin (n+1)→Era G ℝ)(A B:Fin (n+1)→ℝ)
    (debits:∀i,Paid (d i) e (P i) (A i))(kept:∀i,Paid (d i) e (Q i) (B i)):
    let modes:=(univ:Finset (Bits n)).erase (quiet n)
    let pay l:=cost e d (fun i=>if choose n l i then A i else B i)
    let X:=MassP G ℝ n (fun i=>P i+Q i)-MassP G ℝ n Q
    X=∑l∈modes,placed P Q l ∧ Paid (∑i,d i) e X (∑l∈modes,pay l):=by
  classical
  intro modes pay X
  have each (b:Bits n):Paid (∑i,d i) e (placed P Q b) (pay b):=by
    exact original d (fun i=>if choose n b i then P i else Q i)
      (fun i=>if choose n b i then A i else B i) (fun i=>by
        cases h:choose n b i with
        | false=>simpa only [Bool.false_eq_true,if_false] using kept i
        | true=>simpa only [if_true] using debits i)
  have split:X=∑l∈modes,placed P Q l:=by
    have h:=sum_erase_add (s:=(univ:Finset (Bits n))) (f:=placed P Q) (mem_univ (quiet n))
    rw [WilsonIndependentMatchedRosterMasks.fitted] at h
    exact sub_eq_iff_eq_add.mpr ((WilsonIndependentMatchedRosterMasks.deposited n P Q).trans h.symm)
  refine ⟨split,?_⟩
  rw [split]
  refine ⟨Auth.sum (fun b _=>(each b).1),sum_nonneg (fun b _=>(each b).2.1),?_⟩
  intro j hj r hr
  have joined:=Fruit.sum (fun b (_:b∈modes)=>(each b).2.2 j hj r hr) (le_rfl:0 ≤ (0:ℝ))
  simpa only [Prod.snd_sum,Finset.sum_apply] using joined

end YM.Integration.WilsonOlderFreshSoftSocketVerseProduct
