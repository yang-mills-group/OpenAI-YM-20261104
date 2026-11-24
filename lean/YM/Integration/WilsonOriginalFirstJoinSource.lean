import YM.Integration.WilsonOriginalSignedHardWithdrawal
import YM.Integration.WilsonOriginalSeparatedHardRadius
import YM.Integration.WilsonOriginalSeparatedHardSuccessor
import YM.Integration.WilsonRootedKioskFreeRadius

/-! Restore the true mark radii after the tested outgoing shift has
been charged to the original second merger. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFirstJoinSource
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
    {V I : Type} {α : Type} [DecidableEq V] [Countable I] {R : Marker.Census V}
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


open WilsonOriginalSeparatedHardSuccessor
local notation "erased" => without H W eye A rad old hr slots degree income u shift test

theorem original {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    {factor:ℝ} (one:1≤factor) (fare:shift.Budget (Stoop.radius rad factor) P'.p.B (α₁+1) s)  {index:Type*} (E:Lamps α index G P'.p (S.ratio.parent ∘ o) R) :
    WilsonOriginalForcedMarkerPrice.Invoice erased (actual).K rad P'.p.B α₁
       ((Real.exp (θ*depth))⁻¹*(2*(factor^k*r))) ∧
    ∀ t Z,
      let kept:Gallery α index (S.ratio.parent ∘ o) P' R:=⟨E,(actual).K⟩
      let gone:Gallery α index (S.ratio.parent ∘ o) P' R:=⟨E,erased⟩
      kept.density t Z-gone.density t Z=
        (Complex.ofReal (Real.exp (P'.exponent Z))) •
          (Poly.pass (E.log t Z)*∑' I:Finset ℕ,
           WilsonOriginalSignedHardWithdrawal.selected erased (actual).K t Z I) := by
  let target := raised A test H eye rad old hr slots income u tariff apart
  have st := WilsonOriginalForcedMarkerIntake.actual use H Chi.canonical eye.pad M u eye.bells H Ω
    P'.p eye.block eye.pole W.entrance W.offer axis choir toll (occupied A test rad rests) m₁ m₀ target
  have mid := WilsonOriginalForcedMarkerMerger.first _ _ _ st W.first
  have later := WilsonOriginalForcedMarkerMerger.second _ _ _ mid shift W.second
  have prices (l:Trigger.Table A×Bool→ℝ) {τ:ℝ} (m:Motto (brand M u) l 0 H τ K Y eye.sight) :
      (post l m).Paid rad P'.p.B α₁ (factor^k*r) := by
    have cover := Lanes.layoutK_price H Chi.canonical eye.pad M u l eye.bells m H Ω P'.p eye.block
      eye.pole W.entrance W.offer axis choir toll
    have site := WilsonOriginalForcedMarkerPrice.first (bill l m) W.first hr
      (add_nonneg P'.p.exponent_pos.le zero_le_one) (Hard.mono _ cover eye.room)
    have lower := Stoop.leaves rad _ hr one site
    have final := WilsonOriginalForcedMarkerPrice.second _ shift W.second
      (fun j=>div_pos (hr j) (zero_lt_one.trans_le one)) P'.p.exponent_pos.le lower fare
    exact Stoop.budget rad degree (post l m) hr one final
  rw [two_mul]
  constructor
  · simpa only [two_mul] using WilsonOriginalSeparatedHardRadius.restored H W eye A rad old hr slots degree income u
      shift lamp test rests tariff apart one fare
  · intro t Z
    apply WilsonOriginalSignedHardWithdrawal.held (v:=v) erased (actual).K E (prices del m₀)
      (prices base m₁) hr
    intro i j outside
    have relation:=later t i Z
    change (((post base m₁).hard t i Z)-((post del m₀).hard t i Z)).part j=0
    rw [relation.value,add_sub_cancel_left,Poly.part_smul,relation.marked j outside,mul_zero]

variable {J₂:Type} [Countable J₂]
variable (newborn:Lamps α J₂ G P'.p (S.ratio.parent ∘ o) R)
local notation "full" => WilsonRootedKioskSlipCharge.roll shift newborn
local notation "old0" => without H W eye A rad old hr slots degree income u full test
local notation "entry" => Travel.mid H W eye A rad old hr slots degree income u

theorem physical {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    {baseFee fee:ℝ} (prior:shift.Budget rad P'.p.B (α₁+1) baseFee)
    (added:WilsonRootedKioskOccupiedSlip.Gross newborn rad P'.p.B (α₁+1) fee) (margin:0<s) (extra:ℝ) {index:Type*} (E:Lamps α index G P'.p (S.ratio.parent ∘ o) R) :
    let factor:=WilsonRootedKioskFreeRadius.radius extra baseFee fee s
    WilsonOriginalForcedMarkerPrice.Invoice old0 (Kiosk.Second.canopy entry full W.second)
      rad P'.p.B α₁ ((Real.exp (θ*depth))⁻¹*(2*(factor^k*r))) ∧
    ∀ t Z,
      let kept:Gallery α index (S.ratio.parent ∘ o) P' R:=⟨E,Kiosk.Second.canopy entry full W.second⟩
      let gone:Gallery α index (S.ratio.parent ∘ o) P' R:=⟨E,old0⟩
      kept.density t Z-gone.density t Z=
        (Complex.ofReal (Real.exp (P'.exponent Z))) •
          (Poly.pass (E.log t Z)*∑' I:Finset ℕ,
           WilsonOriginalSignedHardWithdrawal.selected old0 (Kiosk.Second.canopy entry full W.second) t Z I) := by
  intro factor
  obtain ⟨one,_,price⟩:= WilsonRootedKioskFreeRadius.original shift newborn hr prior added margin extra
  exact original H W eye A rad old hr slots degree income u full newborn test rests tariff apart one price E

end YM.Integration.WilsonOriginalFirstJoinSource
end
