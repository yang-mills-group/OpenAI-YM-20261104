import YM.Integration.WilsonNeutralTwoPrintPathInherited

/-! The previously declared and reprinted connected words, with their actual
old Laurent masses, supply the entire input for the temporary squarefree log. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralTwoPrintPathInheritedBlocks
open Function Finset Filter Lattice RG Laurent Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonNeutralTwoPrintPathInherited (atom)
open WilsonNeutralTwoPrintPathRebadge (table)
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}{D k:Fin n→ℕ}{e:ℕ}
variable {I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}

def gathered (Y:Outerm G D)(k:Fin n→ℕ)(e:ℕ)(J:I→Finset (Fin n))(c:I→Fin n)
    (sites:I→Fin n → Cover)(read:(i:I)→Pen D (J i) →L[ℝ] Vote (H i)):Outerm G H:=
  table (fun i=>atom Y k e (sites i) (J i) (c i) (read i))

def amount (B:ℝ)(J:I→Finset (Fin n))(read:(i:I)→Pen D (J i) →L[ℝ] Vote (H i)):ℝ:=
  1+∑i,‖read i‖*B^(J i).card

theorem original (Y:Outerm G D)(well:Wellness k Y){s B:ℝ}(hs:0<s)(hB:1 ≤ B)
    (bill:CoverBill Y e s B)(J:I→Finset (Fin n))(c:I→Fin n)(live:∀i,c i∈J i)
    (sites:I→Fin n → Cover)(read:(i:I)→Pen D (J i) →L[ℝ] Vote (H i)):
    let X:=gathered Y k e J c sites read
    let A:=amount B J read
    1 ≤ A ∧ Wellness (fun i=>mass k (J i)) X ∧ CoverBill X e s A:=by
  intro X A
  have bp:0 ≤ B:=zero_le_one.trans hB
  have nonneg(i:I):0 ≤ ‖read i‖*B^(J i).card:=by positivity
  have enough:1 ≤ A:=by
    change 1 ≤ 1+∑i,‖read i‖*B^(J i).card
    linarith [Finset.sum_nonneg (fun i (_:i∈(Finset.univ:Finset I))=>nonneg i)]
  have covers(i:I):‖read i‖*B^(J i).card ≤ A:=by
    change _ ≤ 1+∑i,‖read i‖*B^(J i).card
    linarith [Finset.single_le_sum (f:=fun i=>‖read i‖*B^(J i).card) (fun i _=>nonneg i) (Finset.mem_univ i)]
  have paid(i:I):=WilsonNeutralTwoPrintPathInherited.posted Y well hs hB bill (sites i) (J i) (c i) (live i) (read i)
  exact ⟨enough,WilsonNeutralTwoPrintPathRebadge.issued _ (fun i=>(paid i).1) hs.le (zero_le_one.trans enough)
    (fun i a ha r=>((paid i).2 a ha r).cost (covers i))⟩

theorem reading (Y:Outerm G D)(k:Fin n→ℕ)(e:ℕ)(J:I→Finset (Fin n))(c:I→Fin n)
    (sites:I→Fin n → Cover)(t:I→Case D)(pay:(i:I)→Vote (H i))(i:I)(z:I → Cover)(u:Case H)(g:Side):
    pPly u {i} (((gathered Y k e J c sites (fun i=>(touch (t i) (J i)).smulRight (pay i))) z {i}).1 g)=
      (pay i (u i)) • WilsonReceivedDepositedOrbitalPages.offered Y k e (sites i) (t i) (J i) (c i) g (wrap g (z i)):=by
  unfold gathered
  rw [WilsonNeutralTwoPrintPathRebadge.one]
  funext a r q
  change touch u {i} (petal H i (((touch (t i) (J i)).smulRight (pay i)) _))=_
  rw [petal_hit,ContinuousLinearMap.smulRight_apply]
  change _ * pay i (u i)=pay i (u i) * touch (t i) (J i) _
  rw [mul_comm]
  congr 3
  let M:=((submit Y k e (sites i) (J i)).1 g a r)
  change M _=M _
  apply congrArg M
  funext l
  apply Prod.ext
  · change -(wrap g (-(sites i (c i))))+(-(wrap g (z i))+(q l).1)=-(wrap g (z i)-wrap g (sites i (c i)))+(q l).1
    rw [map_neg,neg_neg]
    abel
  · rfl

end YM.Integration.WilsonNeutralTwoPrintPathInheritedBlocks
end
