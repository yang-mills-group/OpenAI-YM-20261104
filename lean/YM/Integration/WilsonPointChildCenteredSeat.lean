import YM.Integration.WilsonPointChildCenteredSeam
import YM.Integration.WilsonPointChildCenteredBasis
import YM.Integration.WilsonPointChildDigitIncome
import YM.Integration.WilsonPointChildNamedSalary
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildHalfCell
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredSeat
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestJet WilsonPointChildTestCoordinates WilsonCoeffUV.Wheel.Mark
variable {ι:Type}

open WilsonPointChildNamedBasis WilsonPointChildCenteredBasis
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildCenteredFunctional (issue seat)
open WilsonMarkedIndependentNormalizedScale (rate)
open Bloch
variable {r:ℕ}
open Filter Function
private theorem translated {V:Type*}[NormedAddCommGroup V]{α:Type} (v: Cover){P: Ten V (Cloth α) r}(n:Side): Carp.plume (revolve v P) n= revolve (wrap n v) (Carp.plume P n):= by
    classical
    let B: Equiv.Perm (dock Cover α r) := (Equiv.refl (Fin r)).arrowCongr (jog v); funext x; rw [Carp.plume,← B.tsum_eq]; unfold revolve Carp.plume
    apply tsum_congr; intro y; unfold peglet; change (if slideC n (jog v ∘ y)=x then P (jog (-v) ∘ (jog v ∘ y)) else 0)=(if slideC n y=jog (-wrap n v) ∘ x then P y else 0)
    have ht : slideC n (jog v ∘ y)=jog (wrap n v) ∘ (slideC n y):= funext fun i=> fold_move n v (y i)
    have he{A W:Type}[AddGroup A](x:dock A W r)(p:A): jog (-p) ∘ (jog p ∘ x)=x:= by ext i <;> simp [jog]
    have hs: slideC n (jog v ∘ y)=x ↔ slideC n y=jog (-wrap n v) ∘ x :=⟨fun p=> by rw [← p,ht]; exact (he ..).symm,fun p=>by rw [ht,p]; simpa only [neg_neg] using (he x (-wrap n v))⟩
    split_ifs with hv hu hu; rw [he]; apply False.elim; exact hu (hs.mp hv); apply False.elim; exact hv (hs.mpr hu); rfl

theorem placed (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι→ℕ)(s:ι)(depth:k<h s)
    (digit:∀i,Site (R.family.S.block i))(N j:ℕ)(v:Letter (R.family.labels.level k))(z:Cover):
    seat R u k h s depth digit N j v z=shifted (issue R u k h s depth digit N j v) z:=by
  apply Prod.ext
  · funext n e r x
    simp only [WilsonPointChildCenteredFunctional.seat,WilsonPointChildCenteredFunctional.issue,Prod.fst_sum,Finset.sum_apply,shifted,tuftV,ply,skewV,revolve]
    exact Finset.sum_congr rfl fun _ _=>rfl
  · funext e r x
    simp only [WilsonPointChildCenteredFunctional.seat,WilsonPointChildCenteredFunctional.issue,Prod.snd_sum,Finset.sum_apply,shifted,tuftV,ply,skewV,revolve]
    exact Finset.sum_congr rfl fun _ _=>rfl

theorem original (R:Run G)(u:G.ColorIndex)(k E:ℕ)(h:ι→ℕ)(s:ι)(depth:k<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple:G.Simple)(price:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
    (finite:WilsonPointChildDigitHierarchy.Filed R):
    ∀ᶠj:ℕ in atTop,∀(digit:∀i,Site (R.family.S.block i)) N per,j≤N →
    ∀(v:Letter (R.family.labels.level k)) e,e≤E → ∀r x z,
    let n:=R.family.side j per
    let X:=seat R u k h s depth digit N j v z
    ‖X.1 n e r x-Carp.plume (X.2 e r) n x‖≤
      (∑t:Spring (h s),(1+WilsonPointChildCenteredSalary.bill t))*rate R.family.path.levels j per:=by
  filter_upwards [WilsonPointChildCenteredSeam.original R u k E h s depth o tags simple price paid finite] with j seated
  intro digit N per live v e he r x z n X
  dsimp only [X]
  rw [placed]
  change ‖revolve (wrap n z) ((issue R u k h s depth digit N j v).1 n e r) x-
    Carp.plume (revolve z ((issue R u k h s depth digit N j v).2 e r)) n x‖≤_
  rw [translated]
  exact seated digit N per live v e he r _

end YM.Integration.WilsonPointChildCenteredSeat
