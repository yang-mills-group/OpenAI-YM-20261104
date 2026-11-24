import YM.Integration.WilsonNeutralTwoPrintPathFineFiber
import YM.Integration.WilsonNeutralTwoPrintPathFineGrades
import YM.Integration.WilsonReceivedDepositedOrbitalFixedLabels

/-! All occupied subfaces of the actual, individually based inherited
inputs agree with submissions on their own fixed child digits, through
the purchased thermal degree and at every held angular coefficient. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonNeutralTwoPrintPathFineSubmission
open Function Filter Finset Lattice RG Wilson Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonReceivedCompactVerseEntrance (submit CoverBill)
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered)
open WilsonNeutralTwoPrintPathFineFiber (seats fine)
open WilsonReceivedDepositedOrbitalFixedLabels (home)
open WilsonReceivedCoverGrade (Through)
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}{I:Type}[Fintype I][DecidableEq I]{D k:Fin n→ℕ}{H:I→ℕ}{e:ℕ}

theorem entry (Y:Outerm G D)(well:Wellness k Y){s B:ℝ}(hs:0<s)(one:1≤B)
    (bill:CoverBill Y e s B)(J:I→Finset (Fin n))(c:I→Fin n)(live:∀i,c i∈J i)
    (sites:I→Fin n → Cover)(read:(i:I)→Pen D (J i) →L[ℝ] Vote (H i))(S T:Finset I)(inside:T⊆S)
    (F:Side)(x z:I → Cover)(same:∀i∈S,wrap F (x i)=wrap F (z i)):
    let A:=gathered Y k e J c sites read
    Through e ((A x T).1 F) (((submit A (fun i=>mass k (J i)) e) z T).1 F):=by
  intro A a within
  funext r
  rw [WilsonNeutralTwoPrintPathInheritedPeriod.original Y well hs one bill J c live sites read z T within F r]
  dsimp only [A,gathered]
  by_cases active:∃i,T={i}
  · obtain ⟨i,rfl⟩:=active
    rw [WilsonNeutralTwoPrintPathRebadge.one,WilsonNeutralTwoPrintPathRebadge.one]
    simp only [cn,shifted,skewV,same i (inside (Finset.mem_singleton_self i))]
  · have off:∀i,T≠{i}:=fun i h=>active ⟨i,h⟩
    rw [WilsonNeutralTwoPrintPathRebadge.dark _ _ _ off,WilsonNeutralTwoPrintPathRebadge.dark _ _ _ off]

theorem original (Y:Outerm G D)(well:Wellness k Y){s B:ℝ}(hs:0<s)(one:1≤B)
    (bill:CoverBill Y e s B)(J:I→Finset (Fin n))(c:I→Fin n)(live:∀i,c i∈J i)
    (sites:I→Fin n → Cover)(read:(i:I)→Pen D (J i) →L[ℝ] Vote (H i))
    {n₀ f X F:Side}(P:Patch)(u:f.val=n₀.val*P.L.val)(v:F.val=X.val*P.L.val)(h:n₀.val∣X.val)(Hf:f.val∣F.val)
    (S:Finset I)(address:I→Site f)(p:S→Fin (Pages f F))(anchor:S)(T:Finset I)(inside:T⊆S):
    let A:=gathered Y k e J c sites read
    let wanted:=home S Hf address p
    let input:=chartIn P (seats P v h Hf S address p anchor) (fun i=>(Ratio.mk P.L u:Ratio n₀ f).residue (address i))
    let stamped:=(submit A (fun i=>mass k (J i)) e) input
    Through e ((A wanted T).1 F) ((stamped T).1 F) ∧
      Through e ((levelsO (A wanted) T).1 F) ((levelsO stamped T).1 F):=by
  intro A wanted input stamped
  have located (i:I)(owns:i∈S):wrap F (wanted i)=wrap F (input i):=
    (WilsonNeutralTwoPrintPathFineFiber.original P u v h Hf S address p anchor ⟨i,owns⟩).symm
  have registered (t:Finset I)(owns:t⊆S):Through e ((A wanted t).1 F) ((stamped t).1 F):=
    entry Y well hs one bill J c live sites read S t owns F wanted input located
  exact ⟨registered T inside,WilsonNeutralTwoPrintPathFineGrades.ordinary T (fun t ht=>registered t (ht.trans inside))⟩

end YM.Integration.WilsonNeutralTwoPrintPathFineSubmission
end
