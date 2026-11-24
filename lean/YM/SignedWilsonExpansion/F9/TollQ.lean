import YM.SignedWilsonExpansion.F9.Tock
import YM.FVA2.Main
/-!
# Pay quotation in arbitrary d frames and masks. Exact preposition prescription,
 at this stage NO resetting.Clock/calendar is an independent removal.<Accuracy.Price> derivative-order separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission.TollQ
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Asymptotics
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Mer.Xa.MarqueQ
variable {G:Gauge}{n d i l:ℕ}{ι:Type} {L:Filter ι}
variable (H : G.Simple) (W':Initialize G){P':Normalize.Store G}(K:Rose.Pick P')
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (S : Prescription (Press.portDeck G)) {dial: Bool}
variable (ν:ℝ) (M:Speed.Quoted W' K T S) -- order
variable (U:Set (Points n)) (x:ι→ Sample n) (p:ι→ Stage n)
structure Seats (L:Filter ι) (x:ι→Sample n)(p:ι→Stage n)(U:Set (Points n)):Prop where
     comp : IsCompact U
     safe : U⊆conf n
     pose : Tendsto x L (Speed.Pose U)
     align : ∀ᶠ i in L,familiar (x i)=(p i).val
section play
variable (sx:Seats L x p U)(D:Tags G d n)
local notation "Tᵥ"=> Measure.start W' K d
include sx M
lemma score : Speed.Quotes ν W' K S T D U := M.funds _ ν _ sx.comp sx.safe
include ν H
omit sx in
lemma tuner (X:Stage n) : Reg.Faith.rate ν K T d X.val = Tᵥ n X:=by obtain ⟨hs,hr,hu⟩:= M.toContract.toMission.born; rw [ ← Measure.together W' K ν T S H hs hr hu _ ]; rfl
include sx H M
lemma price (k:ℕ) :
   let Z(i):= MS.Tide.mildG*(x i).F.spacing -- not used
   (fun i=> (Rose.measureₓ W' K d (x i) k D) - Tᵥ n ( p i ) k D)=O[L] (Speed.chip ∘ grab ∘ x) ∧
   (fun i=> Tᵥ n (p i) k D)=O[L] (1:ι→ℝ):=by
    intro Z
    let Pᵣ (x:Points n):= Reg.Faith.rate ν K T d x k D
    let F(i):= Pᵣ (familiar i); have hz:(fun i=> F (x i))=ᶠ[L] fun i=> Tᵥ n (p i) k D:= sx.align.mono fun i hi=> by dsimp only [F,Pᵣ]; rw [hi,tuner H W' K T S ν M (d:=d) (p i)] -- include H
    have hx := ((Speed.cartel.mp ((score W' K T S ν M U x p sx D).clocks k).1).comp_tendsto sx.pose); refine ⟨IsBigO.congr' hx (( EventuallyEq.rfl (f:=fun i=> Rose.measureₓ W' K d (x i) k D)).sub hz) (.refl ..), ?_⟩
    have hp:ContinuousOn Pᵣ (conf n):= fun x hx=> (Speed.Timeframe.cash ν K T D x hx k).continuousAt.continuousWithinAt
    refine IsBigO.congr' (IsBigO.comp_tendsto (Speed.essence (conf n) Pᵣ U sx.comp sx.safe hp) sx.pose) hz (.refl ..)
end play
end YM.SignedWilsonExpansion.Commission.TollQ
