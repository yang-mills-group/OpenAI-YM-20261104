import YM.Integration.WilsonNeutralTwoPrintPathInheritedBlocks
import YM.Integration.WilsonPointChildCenteredSeat

/-! Reissuing the finite catalogue of whole previous depositions preserves
its actual finite-period coefficients before the next Gaussian integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonNeutralTwoPrintPathInheritedPeriod
open Function Finset Filter Lattice RG Laurent Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonNeutralTwoPrintPathInherited (atom)
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open private translated from YM.Integration.WilsonPointChildCenteredSeat
open private center from YM.Integration.WilsonNeutralTwoPrintPathInherited
open scoped Classical BigOperators

variable {G:Gauge}{n:ℕ}{D k:Fin n→ℕ}{e a r:ℕ}{X:Side}
variable {I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}
variable {V W:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
  [NormedAddCommGroup W][NormedSpace ℝ W][CompleteSpace W]

omit [CompleteSpace W] in
private theorem mapped (Z:Era G V)(T:V→L[ℝ]W){s A:ℝ}{o:Cover}
    (width:0<s)(bill:Cork Bank.terrain o s A (Z.2 a r))
    (record:Z.1 X a r=plume (Z.2 a r) X):
    (tuftV T Z).1 X a r=plume ((tuftV T Z).2 a r) X:=by
  change T ∘ Z.1 X a r=plume (T ∘ Z.2 a r) X
  rw [record,plume_map _ bill width T X]

omit [NormedSpace ℝ V] [CompleteSpace V] in
private theorem moved (Z:Era G V)(o:Cover)(record:Z.1 X a r=plume (Z.2 a r) X):
    (shifted Z o).1 X a r=plume ((shifted Z o).2 a r) X:=by
  change revolve (wrap X o) (Z.1 X a r)=plume (revolve o (Z.2 a r)) X
  rw [record,translated]

theorem original (Y:Outerm G D)(well:Wellness k Y){s B:ℝ}(hs:0<s)(hB:1 ≤ B)
    (bill:CoverBill Y e s B)(J:I→Finset (Fin n))(c:I→Fin n)(live:∀i,c i∈J i)
    (sites:I→Fin n → Cover)(read:(i:I)→Pen D (J i) →L[ℝ] Vote (H i))(y:I → Cover)(S:Finset I)
    (within:a ≤ e)(X:Side)(r:ℕ):
    let T:=gathered Y k e J c sites read
    let salary:=fun i=>mass k (J i)
    ((submit T salary e y S).1 X a r)=(T y S).1 X a r:=by
  intro T salary
  have intake:=WilsonNeutralTwoPrintPathInheritedBlocks.original Y well hs hB bill J c live sites read
  have mounted:=WilsonReceivedCompactVerseEntrance.original T intake.2.1 hs intake.1 intake.2.2
  rw [(mounted.2.2.1 y S a within).2 X r]
  symm
  by_cases one:∃i,S={i}
  · obtain ⟨i,rfl⟩:=one
    dsimp only [T,gathered]
    rw [WilsonNeutralTwoPrintPathRebadge.one]
    have old:=WilsonReceivedCompactVerseEntrance.original Y well hs hB bill
    let M:Era G (Pen D (J i)):=submit Y k e (sites i) (J i)
    have eqn:M.1 X a r=plume (M.2 a r) X:=by
      obtain ⟨large,finite⟩:=old.2.2.1 (sites i) (J i) a within
      dsimp only [M]
      rw [large,finite]
    have orig:Cork Bank.terrain (sites i (c i)) s (B^(J i).card) (M.2 a r):=by
      dsimp only [M]
      rw [(old.2.2.1 (sites i) (J i) a within).1]
      exact (bill _ _ _ within r).to_cork hs.le (live i)
    let Z:Era G (Pen D (J i)):=shifted M (-(sites i (c i)))
    let P:TowerS G (H i):=tuftV (read i) Z
    have first:Z.1 X a r=plume (Z.2 a r) X:=moved M (-(sites i (c i))) eqn
    have centered:Cork Bank.terrain 0 s (B^(J i).card) (Z.2 a r):=
      center (sites i (c i)) (M.2 a r) orig
    have second:P.1 X a r=plume (P.2 a r) X:=
      mapped (G:=G) (a:=a) (r:=r) (X:=X) Z (read i) hs centered first
    have newPrice:Cork Bank.terrain 0 s (‖read i‖*B^(J i).card) (P.2 a r):=centered.touch (read i)
    let posted:=tuftV (petal H i) P
    have third:posted.1 X a r=plume (posted.2 a r) X:=
      mapped (G:=G) (a:=a) (r:=r) (X:=X) P (petal H i) hs newPrice second
    exact moved posted (y i) third
  · rw [show T y S=0 from WilsonNeutralTwoPrintPathRebadge.dark _ y S (fun i eqn=>one ⟨i,eqn⟩)]
    exact (plume_zero X).symm

end YM.Integration.WilsonNeutralTwoPrintPathInheritedPeriod
end
