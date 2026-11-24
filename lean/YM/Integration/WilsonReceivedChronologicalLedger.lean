import YM.Integration.WilsonReceivedChronologicalConnected

/-! The exact two-stop remainder, with its genuine N-born surplus and remaining change of flat isolated. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalLedger
open Finset MeasureTheory Lattice Wilson RG Labels Source Marker PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonOriginalTwoFlatRoseIdentity (cross)
open WilsonOriginalMicroscopicEntranceDoseBoard (Board source)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntranceTwoExits (originalRead)
open WilsonOriginalMicroscopicEntrancePooledBoard (actual)
open WilsonThermometerCenteredScalar (face)
open scoped Classical BigOperators

def days (b K:ℕ):Finset ℕ:=(Ico b K).image Nat.pred

theorem visited {b K i:ℕ}(bb:0 < b)(hi:i∈days b K): b ≤ i+1 ∧ i+1 < K:=by
  obtain ⟨j,hj,rfl⟩:=mem_image.mp hi
  have :=mem_Ico.mp hj
  simp only [Nat.pred_eq_sub_one]
  omega

theorem previous {T:Type}[AddCommMonoid T]{b K:ℕ}(bb:0 < b)(value:ℕ→T):
    ∑j∈Ico b K,value j=∑i∈days b K,value (i+1):=by
  unfold days
  rw [sum_image]
  · apply sum_congr rfl;intro j hj
    have :=mem_Ico.mp hj;congr 1;simp only [Nat.pred_eq_sub_one];omega
  · intro x hx y hy eq
    have :=mem_Ico.mp hx;have :=mem_Ico.mp hy;simp only [Nat.pred_eq_sub_one] at eq;omega

theorem combine {T:Type}[AddCommMonoid T]{b a K:ℕ}(ba:b ≤ a)(ak:a ≤ K)(upper lower:ℕ→T):
    (∑j∈Ico a K,upper j)+(∑j∈Ico b a,lower j)=∑j∈Ico b K,if a ≤ j then upper j else lower j:=by
  have setEq:Ico b K=Ico a K∪Ico b a:=by ext j;simp only [mem_Ico,mem_union];omega
  have split:Disjoint (Ico a K) (Ico b a):=disjoint_left.mpr fun j hi lo=>((mem_Ico.mp lo).2.not_ge (mem_Ico.mp hi).1)
  rw [setEq,sum_union split]
  congr 1
  · apply sum_congr rfl;intro j hi;rw [if_pos (mem_Ico.mp hi).1]
  · apply sum_congr rfl;intro j hi;rw [if_neg (mem_Ico.mp hi).2.not_ge]

def stop (u b a i:ℕ):ℕ:=if a ≤ i+1 then u else b

theorem scope {u b:ℕ}(ub:u ≤ b)(a i:ℕ):u ≤ stop u b a i ∧ stop u b a i ≤ b:=by
  unfold stop;split <;> omega

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n t:ℕ}{o:Fin 3→Site (R.family.side f per)}
  (B:Board R d N per f o t)(v:∀i:Fin 3,R.family.label (d i))(c:Fin 3→ℂ)
  (past:∀j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))
local notation "table" => WilsonReceivedChronologicalPlant.rows R d (n:=n) (N:=N) o v c past
local notation "atW" s:max => WilsonReceivedChronologicalReadout.face R N per (table) (face s)
local notation "owed" i:max => WilsonOriginalJointTrialHearing.fee R N per (v:=i) 1 (table)

def remaining {u b a:ℕ}(uf:u ≤ f)(ua:u ≤ a)(ba:b ≤ a)(aK:a ≤ f+n)(active:f+n ≤ N)
    (s:Finset (Fin 3))(target:ℂ):ℂ:=
  gap R N per u ((ua.trans aK).trans active) (actual R d B (face s) c)+
  mass c (face s)*originalRead R d (p:=per) (f:=f) (n:=n) active (source R B) o v (face s) uf 1+
  cross R (N:=N) ua ba (atW s)+((atW s) b 1-target)

theorem original {u b a:ℕ}(bb:0 < b)(uf:u ≤ f)(ua:u ≤ a)(ba:b ≤ a)(aK:a ≤ f+n)(active:f+n ≤ N)
    (s:Finset (Fin 3))(target:ℂ):
    WilsonReceivedChronologicalConnected.line R d B v c past uf ua ba aK active s target-
      remaining R d B v c past uf ua ba aK active s target=
        ∑ i ∈ days b (f+n),(owed (stop u b a i)) (i+1) (face s):=by
  calc
    _ = (∑j∈Ico a (f+n),(owed u) j (face s))+(∑j∈Ico b a,(owed b) j (face s)):=by
      unfold WilsonReceivedChronologicalConnected.line remaining;ring
    _ = ∑j∈Ico b (f+n),if a ≤ j then (owed u) j (face s) else (owed b) j (face s):=
      combine ba aK _ _
    _ = _:=by
      rw [previous bb]
      apply sum_congr rfl;intro i _
      by_cases h:a ≤ i+1
      · rw [if_pos h,show stop u b a i=u from if_pos h]
      · rw [if_neg h,show stop u b a i=b from if_neg h]

end YM.Integration.WilsonReceivedChronologicalLedger
end
