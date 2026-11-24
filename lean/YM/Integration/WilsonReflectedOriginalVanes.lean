import YM.Integration.WilsonReflectedOriginalTwoDeposit
import YM.Integration.WilsonThermometerUnitFilingFourPool

/-! Two independent public measuring stations share one original N/per and the
conditional at K. Each cutoff section is its literal Vane wheel cutoff lift. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOriginalVanes
open GapsContact GapsContact.Seams GapsContact.Stamps
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson Labels Source
open Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical.Germ
open WilsonThermometerUnitFilingFourPool WilsonReflectedOriginalTwoDeposit
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (l:Ultrafilter (ℕ×ℕ))
local notation "C!" => R.family

structure Captured (r B:ℝ)(j m d:ℕ)(v:S.Field d)(Y:ℕ×ℕ→(C!).label d):Prop where
  reference:(C!).ref d≤ j
  physical: ∃(V:∀k:ℕ,Vane (C!) k)(i:ℕ)(h:d ≤ i)(T:Spin.change S d)
      (Z:(Cells.standard (C!)).Field d→L[ℂ](C!).label d),
    (V i).k=j ∧ purchaseWidth (V i)=m ∧ S.project d (Z (T.symm v))=v ∧
    Tendsto (heightV V i d) (l:Filter (ℕ×ℕ)) (𝓝 Z) ∧
    Y=(fun u=>(V i).wheel.atCut u ⟨d,Nat.lt_succ_of_le h⟩ (T.symm v))
  quota:∀N p,j<N→Next.UVStress.quota (C!) d j N p (Y (N,p))≤(C!).S.a j^d*B*cost F d r v
  reflection:∀ᶠ u:ℕ×ℕ in f.fuse,Cards.PaidAt (C!).S u.1 u.2 m ((C!).beta u.1 u.2)
    (B*cost F d r v) ((C!).O u.1 u.2 (Y u) 0)

theorem enrolled {r B j m d}(v:S.Field d)(H:BookedArm F l r j m d B):
    ∃Y,Captured R F l r B j m d v Y:=by
  obtain ⟨V,i,h,T,Z,here,cards,home,limit,bill⟩:=H.station
  let Y:=fun u:ℕ×ℕ=>(V i).wheel.atCut u ⟨d,Nat.lt_succ_of_le h⟩ (T.symm v)
  have purchased:=bill (T.symm v)
  change (_ ∧ _) at purchased
  rw [T.apply_symm_apply] at purchased
  exact ⟨Y,H.owns,⟨V,i,h,T,Z,here,cards,(home _).trans (T.apply_symm_apply _),limit,rfl⟩,purchased.1,purchased.2⟩

def arm {d N p:ℕ}(Y:ℕ×ℕ→(C!).label d)(hand:Bool)(g:Signed)(pin:Site ((C!).side N p)):Column R N p d:=
  ⟨Y (N,p),hand,g,pin⟩

theorem original {ra rb Ba Bb ja jb ma mb da db}(a:S.Field da)(b:S.Field db)
    (left:BookedArm F l ra ja ma da Ba)(right:BookedArm F l rb jb mb db Bb):
    ∃Y Z,Captured R F l ra Ba ja ma da a Y ∧ Captured R F l rb Bb jb mb db b Z ∧
      ∀{N p K},∀ H:K≤ N,∀h₁ h₂:Bool,∀s₁ s₂:Signed,∀x y:Site ((C!).side N p),
      let one:=arm R Y h₁ s₁ x
      let two:=arm R Z h₂ s₂ y
      ∀U,actualTransport (C!) (N:=N) (fun W=>raw R one W*raw R two W) H U-separate R one two K U =
       ∑i∈Finset.Ico K N,landed R one two K i U:=by
  obtain ⟨Y,first⟩:=enrolled R F l a left
  obtain ⟨Z,second⟩:=enrolled R F l b right
  refine ⟨Y,Z,first,second,?_⟩
  intro N p K H h₁ h₂ s₁ s₂ x y one two U
  exact WilsonReflectedOriginalTwoDeposit.original R
      (arm R Y h₁ s₁ x) (arm R Z h₂ s₂ y) H U

end YM.Integration.WilsonReflectedOriginalVanes
