import YM.Integration.WilsonOriginalHardOwnerSuccessor

/-! A separated mixed forced address on the actual QuadraticLocal gallery. All eligible
owners and both real components enter the single charged return. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedHardReturn
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger
open WilsonOriginalHardOwnerReweight WilsonOriginalHardOwnerSuccessor
open scoped Topology BigOperators Classical

variable {G : Gauge} {n c L : Side} {S : StepData c n} {C : Teller G}
    {D : Tube G S} {P : Rep G n} {P' : Rep G c} {w x κ z e f r s Y Γ K b b' : ℝ}
    {Q : ConnectedActivityE6.Target G C} {h : ConnectedActivityE6.Target.Order G w}
    {V I : Type} {α : Type*} [DecidableEq V] [Countable I] {R : Marker.Census V}
    {o : V → Site n} {k depth : ℕ}

variable (A : Gallery α I o P R) (test : R.Mode → Prop)
def owned (i : Trigger.Table A × Bool) : Prop :=
  i.1.elim (fun _=>False) (fun j=>test j.val.2)

variable (H : Cash w x κ L Q h z D P) (W : Travel.Walk H P' e f r s)
    (eye : Travel.Eyes H P' e Γ Y K k) (rad : V → ℝ) (old : Travel.Seal A rad b b')
    (hr : ∀ v,0<rad v) (slots : HasSlots P.p P.activities) (u : α)
local notation "M" => Trigger.listCosts A rad hr slots old.supE old.crown
    (Travel.sighting A rad old) old.looks
local notation "M₀" => brand M u
local notation "Θ" => P.p.supportExponent/8
local notation "Ω" => Match.staple (H:=H) («J»:=H) rfl rfl rfl
local notation "plant" => kettle H Chi.canonical M u (fun _=>1) Set.univ 0 H Ω W.entrance W.offer

/-- The signed real and imaginary leaves sit on the genuine complete support
of their old hard address. The cover lower bound is uniform in that address. -/
theorem covered (apart : ∀ t:R.Mode,test t →
    ∃ v∈t.val,∃ w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w)) :
    ∀ i, owned A test i → depth≤coverNumber P.p.B ((M₀) i).crest := by
  rintro ⟨i|i,parity⟩ hit
  · exact False.elim hit
  · obtain ⟨v,hv,w,hw,dist⟩ := apart i.val.2 hit
    change depth≤coverNumber P.p.B ((Trigger.wing A (Sum.inr i,parity)).support P)
    rw [Trigger.wingE A slots]
    have span := dist.trans (Corona.extent (P.activities.forced i.val.1).support P.p.B
      (i.prop.2 v hv) (i.prop.2 w hw))
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right span) (by omega)

include eye in
/-- The actual temporal tariff and one spatial invoice on the same funded
forced arrays. Both merger witnesses are the ones in the supplied Walk. -/
theorem original (income : 2*(b+b')≤K) (foam : Daisy.foam Q L) (pot : 4≤Q.relative)
    (apart : ∀ t:R.Mode,test t →
      ∃ v∈t.val,∃ w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w)) :
    Yard.Pays (marked (owned A test) plant) Set.univ k P'.p.B
      (P'.p.supportExponent+1+1) (Real.exp (-(Θ*depth))*e) := by
  let use := owned A test
  have bank := Travel.fiscal H eye A rad old hr slots income u
  obtain ⟨carrier,cf,entry,rows,cap⟩:= bank.claim
  letI : Fintype carrier := cf
  have hθ : 0≤Θ := div_nonneg P.p.exponent_pos.le (by norm_num)
  have cap' := WilsonOriginalHardOwnerReweight.scale cap hθ use
    (covered A test rad old hr slots u apart)
  have target := WilsonOriginalHardOwnerReweight.funded Q foam pot
    (Q.grants.1.le.trans_eq H.laws.intake.exponent)
  have rich : Motto (M₀) (raise use Θ depth) 0 H (P.p.supportExponent-Θ) K Y eye.sight :=
    ⟨⟨carrier,cf,entry,rows,cap'⟩,target,le_rfl,by simp,by simp⟩
  obtain ⟨bill,pos,pace,values⟩ := (received use H Chi.canonical eye.pad M u eye.bells H Ω
    W.entrance W.offer hθ rich P'.p eye.block).wages
  exact ⟨bill,pos,(fun y=>budget_loosen (pace y)
    (mul_le_mul_of_nonneg_left eye.room (Real.exp_pos _).le)),values⟩

end YM.Integration.WilsonOriginalSeparatedHardReturn
end
