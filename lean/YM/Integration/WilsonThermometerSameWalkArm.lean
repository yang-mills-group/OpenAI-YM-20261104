import YM.Integration.WilsonThermometerSameWalkGerm
import YM.PECompat4984.Donor.Tickets
import YM.Integration.WilsonThermometerOwnOffsetField
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkArm
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG.Shoot
open Extra.Histories Relay PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open ProjectorNext.Equivariance Next.Foundations Push.CutoffProjectors
open scoped Topology Classical
variable {G:Gauge}

theorem moved {d:ℕ} {nn:Side} (F:Frame G d) (A:Hol G) (o:Site nn) (q:Coefficient F nn)
    {W:Rep G nn} (move:W.activities.Moves 1 o) (θ:ℝ) :
    projection F A θ o (shifted move q)=projection F A θ 0 q:=by
  change turn F 1 q.x+(∑' j,vector F A θ o (q.regular j ∘ pull 1 o))=q.x+∑' j,vector F A θ 0 (q.regular j)
  have translateLinks:(pull 1 o:Config G nn → Config G nn)=Lattice.translate o:=funext (Lattice.pull_one o)
  rw [turn_one,translateLinks]
  apply congrArg (q.x+·)
  apply tsum_congr
  intro j
  apply congrArg (fun w=>F.scaled θ (F.coords w))
  suffices h:label A (0+o) (q.regular j ∘ Lattice.translate o) d=label A 0 (q.regular j) d by
    simpa only [zero_add] using h
  let chooseJet (Q:Label G d→Prop):=if h:∃u,Q u then h.choose else 0
  change chooseJet (fun w=>JetTest A (0+o) w (q.regular j ∘ Lattice.translate o)) =
    chooseJet (fun w=>JetTest A 0 w (q.regular j))
  apply congrArg chooseJet
  funext w
  simp only [JetTest,comp_apply,Drift.test_translate]

open RG12 RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local MergeProof Accent
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField WilsonThermometerOffsetResidue

variable (R:Run G) {d base i N per:ℕ}
local notation "C" => R.family
local notation "F" => R.family.labels.level d

/-- The intrinsic engineering-normalized microscopic field at the elected
child, viewed at this actual age. -/
def enteredField (z:Site ((C).side N per)) (r:Emblems (C) d) (live:i ≤ N)
    (v:Palette (C) d):Config G ((C).side i per) → ℂ:=
  let x:=((C).factory d N per).terminal (finer r live v (primaryLetter d))
  dyes (C) i N per live (((C).S.a i:ℂ)^d • (C).O N per x z)

theorem enrolled {D:Rail (C)} {B:ℕ→ℕ→ℝ} {V:Sight (C) d per} {r:Emblems (C) d}
    (z:Site ((C).side N per)) (H:Enrolled R.makes D B base N per d (digits R N per z) V r)
    (away:base ≤ i) (live:i ≤ N) (starts:∀ e ≤ d, (C).ref e ≤ N) (v:Palette (C) d) :
    let P:=(C).path.rep N per i
    let o:=((C).S.toDepth live per).parent z
    ∃ Z:Coefficient (F) ((C).side i per), ∃ b:ℝ,
      Z.Format o (C).params P ∧ Z.remBound o P (kappa (C).path i) b ∧
      Z.density o ((C).localSection d) P=enteredField R z r live v ∧
      projection (F) (C).params P.p.threshold o Z=v (primaryLetter d):=by
  intro P o
  obtain ⟨X,Q,registered,bare,bill,_,_,atSite,observed⟩:=
    WilsonThermometerOwnOffsetField.actual R N per i z H away live starts v
  let move:=Classical.choice ((R.makes.wilson.represents N per i live).good.labels.moves 1 o)
  let Z:=shifted move X
  have atHome:affine 1 o 0=o:=by simp [affine]
  have fZ:Z.Format o (C).params P:=atHome ▸ shifted.format move 0 (always_room (C) i per) bare
  have cZ:Z.remBound o P (kappa (C).path i) (permission P.p 1*(B d i*size v)) :=
    atHome ▸ shifted.cap move bare bill
  have exactZ:Z.density o ((C).localSection d) P = X.density 0 ((C).localSection d) P ∘ pull 1 o :=
    (congrArg (fun u=>Z.density u ((C).localSection d) P) atHome.symm).trans
      (shifted.density move ((C).localSection d) (R.makes.sections d) X 0)
  exact ⟨Z,_,fZ,cZ,exactZ.trans (atSite.symm.trans observed),
    (moved (F) (C).params o X move P.p.threshold).trans registered⟩

/-- Both cutoff programs read the same actual palette on every named child.
The inverse of the independent mark radius does not enter this estimate. -/
theorem original {m k:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ j,Rep G ((C).side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started:m ≤ i) (away:base ≤ i) (live:i ≤ N) (ready:(C).ref d ≤ i)
    (starts:∀ e ≤ d, (C).ref e ≤ N) {D:Rail (C)} {B:ℕ→ℕ→ℝ}
    {V:Sight (C) d per} {r:Emblems (C) d} (z:Site ((C).side N per))
    (H:Enrolled R.makes D B base N per d (digits R N per z) V r) (y:Palette (C) d)
    (q:store (C) d per i) {κ a:ℝ}
    (form:q.Format (((C).S.toDepth live per).parent z) (C).params (Ψ i))
    (paid:q.remBound (((C).S.toDepth live per).parent z) (Ψ i) κ a)
    (held:q.density (((C).S.toDepth live per).parent z) ((C).localSection d) (Ψ i) =ᶠ[𝓝 1]
      enteredField R z r live (finer r away y)) :
    let p:=projection (F) (C).params (Ψ i).p.threshold (((C).S.toDepth live per).parent z) q
    p=finer r away y (primaryLetter d) ∧ (F).coeffSize p ≤ stringCost (C) away*size y := by
  intro p
  let P:=(C).path.rep N per i
  let o:Site ((C).side i per):=((C).S.toDepth live per).parent z
  let t:=primaryLetter d
  let v:=finer r away y
  obtain ⟨Z,b,formatZ,feeZ,sourceZ,coordinateZ⟩:=enrolled R z H away live starts v
  have physical:q.density o ((C).localSection d) (Ψ i) =ᶠ[𝓝 1] Z.density o ((C).localSection d) P:=
    held.trans (EventuallyEq.of_eq sourceZ.symm)
  have fixed:p=v t:= (WilsonThermometerSameWalkGerm.actual R π Γ Ψ course started live ready o q Z
      form paid formatZ feeZ physical).trans coordinateZ
  have row:(F).coeffSize (v t) ≤ size v:=by
    rw [bill_group]
    exact Finset.single_le_sum (f:=fun l=>((C).labels.level (kept l)).coeffSize (v l))
      (fun l _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ t)
  exact ⟨fixed,fixed ▸ row.trans (H.inverse le_rfl away live y)⟩

end YM.Integration.WilsonThermometerSameWalkArm
end
