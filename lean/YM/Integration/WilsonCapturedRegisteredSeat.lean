import YM.Integration.WilsonCapturedRegisteredSeed

/-! Periodization of the independent pointed tensor is exactly the sold
finite angular chart at its original displacement, for each marked address. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedRegisteredSeat
open Function Filter Finset Lattice Wilson RG Laurent PowerSeries Bloch WilsonCoeffUV.Cosmos
open FormalBulk08 Flat Reef Jets Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildNamedBasis WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Soil
open WilsonOriginalPlacedPrimerInk WilsonPointChildCenteredFunctional
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}

theorem moved (y:Site n)(P:Gen ℝ (Woods G n))(r:ℕ):
    fade (place y) P r=revolve y (P r):=by
  funext x
  let x₀:=jog (-y) ∘ x
  have back(i:Fin r):WilsonOriginalPlacedPrimerInk.offset y (x₀ i)=x i:=by
    change (y+(-y + (x i).1), (x i).2) = x i
    simp
  change (∑a,(∏ i,place y (a i) (x i)) • P r a)=P r x₀
  rw [Finset.sum_eq_single x₀]
  · simp [place,back]
  · intro a _ neq
    obtain ⟨i,diff⟩:=Function.ne_iff.mp neq
    have h:WilsonOriginalPlacedPrimerInk.offset y (a i)≠x i:=by
      intro same
      apply diff
      apply (jog y).injective
      exact same.trans (back i).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (show place y (a i) (x i)=0 from if_neg h),zero_smul]
  · simp

theorem ground {d:ℕ}(Y:Pot G)(young:Young Y d)(symm:∀e r,Agate (Y e r))(n:Side)(e r:ℕ):
    WilsonOriginalPrimerInk.column d Y n e r=plume (Y e r) n:=by
  rw [←WilsonPointChildFoldedField.folded]
  by_cases hr:r≤d+e
  · rw [WilsonOriginalPrimerInk.column,if_pos hr,sand_fixed (sieve_sand n _ (symm e r))]
  · have vanish:Y e r=0:=by by_contra hn;exact hr (young e r hn)
    rw [WilsonOriginalPrimerInk.column,if_neg hr,vanish,sieve_zero]

variable {ι:Type}(R:Run G)(simple:G.Simple)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
include o simple tags paid in
theorem original (h k:ι→ℕ)(depth:∀s,k s<h s)(u:ι→G.ColorIndex)
    (N j:ℕ)(live:j≤N)(up:∀s,k s≤R.family.path.levels.clock.J j)
    (digit:ι→∀i,Site (R.family.S.block i))(v:∀s,Letter (R.family.labels.level (k s)))
    (films:∀s,Studio (h s)):
    ∃V:Case h,(∀s,‖V s‖≤‖films s‖)∧∀(s:ι)(z:Cover)(n:Side)(e r:ℕ),
      let Z:=seat R (u s) (k s) h s (depth s) (digit s) N j (v s) z
      (touch V {s}) ∘ plume (Z.2 e r) n =
        WilsonOlderFreshPointChart.chart R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s) n (wrap n z) e r:=by
  obtain ⟨V,cap,valid⟩:=WilsonCapturedRegisteredSeed.original R simple o tags price paid h k depth u N j live up digit v films
  refine ⟨V,cap,?_⟩
  intro s z n e r Z
  let X:=issue R (u s) (k s) h s (depth s) (digit s) N j (v s)
  let Y:=WilsonOlderFreshPointGauge.field R (routes R) (u s) (depth s) j (v s) (⟨N,live,digit s⟩,films s)
  let tester:=touch V {s}
  have aligned:tester ∘ X.2 e r=Y e r:=congrArg (fun T:Pot G=>T e r) (valid s).1
  have ward:=WilsonNeutralPointCourse.original R (routes R) (u s) (depth s) (digit s) N j simple o live
    ((up s).trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have shelf:=clef_through (ward.officers (v s)) (slotsFits _ (v s))
  have chart:WilsonOriginalPrimerInk.column (k s) Y n e r=plume (Y e r) n:=
    ground Y (shelf.fare.1 (films s)) (fun e r=>shelf.fare.2.1 (films s) e r) n e r
  have auth:=WilsonPointChildCenteredFunctional.authorized R simple o (u s) (k s) h s (depth s) (digit s) N j live (v s) z
  obtain ⟨w,A,hw,cork⟩:=(auth.wing e r).land
  have undo:tester ∘ Z.2 e r=revolve z (Y e r):=by
    rw [←aligned]
    dsimp only [Z]
    rw [WilsonPointChildCenteredSeat.placed]
    rfl
  change tester ∘ plume (Z.2 e r) n=fade (place (wrap n z)) (WilsonOriginalPrimerInk.column (k s) Y n e) r
  rw [←plume_map _ cork hw tester n,undo,plume_shift,moved,chart]

end YM.Integration.WilsonCapturedRegisteredSeat
