import YM.Integration.WilsonOriginalForcedMarkerWallet

/-! The first actual successor of a separated occupied hard address,
including the two original hard mergers and their unchanged soft partners. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedHardSuccessor
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

open WilsonOriginalForcedMarkerRows WilsonOriginalForcedMarkerMerger
open WilsonOriginalForcedMarkerWallet WilsonOriginalForcedMarkerPrice
variable {J₀ J₁:Type} [Countable J₀] [Fintype V]
variable (H:Cash w x κ L Q h z D P) (W:Travel.Walk H P' e f r s)
    (eye:Travel.Eyes H P' e Γ Y K k) (A:Gallery α I o P R) (rad:V→ℝ)
    (old:Travel.Seal A rad b b') (hr:∀ v,0<rad v) (slots:HasSlots P.p P.activities)
    (degree:∀ t:R.Mode,t.val.card≤k) (income:2*(b+b')≤K) (u:α)
    (shift:Canopy.ShiftRows α J₀ G P'.p (S.ratio.parent ∘ o) R)
    (lamp:Lamps α J₁ G P'.p (S.ratio.parent ∘ o) R)
local notation "M" => Trigger.listCosts A rad hr slots old.supE old.crown (Travel.sighting A rad old) old.looks
local notation "base" => (fun _:Trigger.Table A×Bool=>(1:ℝ))
local notation "Ω" => Match.staple (H:=H) («J»:=H) rfl rfl rfl
local notation "axis" => Trigger.axis A rad
local notation "choir" => Trigger.choir A rad hr k degree
local notation "toll" => (Trigger.colorCosting A S rad slots · P'.p)
local notation "bill" l:max hT:max => Lanes.layoutK H Chi.canonical eye.pad M u l eye.bells hT H Ω P'.p
  eye.block eye.pole W.entrance W.offer axis choir toll
local notation "post" l:max hT:max => Kiosk.Second.canopy (Kiosk.First.led (bill l hT) W.first) shift W.second
local notation "actual" => Travel.respondent H W eye A rad old hr slots degree income u shift lamp
local notation "α₀" => P.p.supportExponent
local notation "α₁" => P'.p.supportExponent
local notation "θ" => P.p.supportExponent/8
variable (test:R.Mode→Prop)
local notation "use" => WilsonOriginalSeparatedHardReturn.owned A test
local notation "del" => omitOwner use
local notation "fat" => raise use θ depth
local notation "m₀" => omitted A test H eye rad old hr slots income u
local notation "m₁" => Travel.fiscal H eye A rad old hr slots income u

/-- Remove exactly the selected mixed forced-input leaves, in both real
components, and preserve the actual intermediate shifts and their partners. -/
def without : Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R := post del m₀

local notation "erased" => without H W eye A rad old hr slots degree income u shift test

theorem original {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    (fare:shift.Budget rad P'.p.B (α₁+1) s) :
    Invoice erased (actual).K rad P'.p.B α₁
      ((Real.exp (θ*depth))⁻¹*(r+r)) := by
  let target := raised A test H eye rad old hr slots income u tariff apart
  have stock := WilsonOriginalForcedMarkerIntake.actual use H Chi.canonical eye.pad M u eye.bells H Ω
    P'.p eye.block eye.pole W.entrance W.offer axis choir toll (occupied A test rad rests) m₁ m₀ target
  have mid := WilsonOriginalForcedMarkerMerger.first _ _ _ stock W.first
  have out := WilsonOriginalForcedMarkerMerger.second _ _ _ mid shift W.second
  have prices (l:Trigger.Table A×Bool→ℝ) {τ:ℝ} (m:Motto (brand M u) l 0 H τ K Y eye.sight) :
      (post l m).Paid rad P'.p.B α₁ r := by
    have covered := Lanes.layoutK_price H Chi.canonical eye.pad M u l eye.bells m H Ω P'.p
      eye.block eye.pole W.entrance W.offer axis choir toll
    have walked := WilsonOriginalForcedMarkerPrice.first (bill l m) W.first hr
      (add_nonneg P'.p.exponent_pos.le zero_le_one) (Hard.mono _ covered eye.room)
    exact WilsonOriginalForcedMarkerPrice.second _ shift W.second hr P'.p.exponent_pos.le walked fare
  apply WilsonOriginalForcedMarkerPrice.paid (v:=v) erased (actual).K (post fat target) _ (inv_nonneg.mpr (Real.exp_pos _).le) hr (prices del m₀) (prices fat target)
  change Related v (↑((Real.exp (θ*depth))⁻¹):ℂ) (post del m₀) (post base m₁) (post fat target)
  simpa only [Complex.ofReal_inv] using out

end YM.Integration.WilsonOriginalSeparatedHardSuccessor
end
