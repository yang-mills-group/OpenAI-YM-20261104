import YM.Integration.WilsonOriginalSignedHardHearing
import YM.QuadraticLocal.Tariff.Measure
import YM.Integration.WilsonOriginalSignedHardWithdrawal
import YM.Integration.WilsonOriginalSeparatedHardRadius
import YM.Integration.WilsonOriginalSeparatedHardSuccessor
import YM.Integration.WilsonRootedKioskFreeRadius

/-! Restore the true mark radii after the tested outgoing shift has
been charged to the original second merger. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRaisedHardPost
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

theorem at_radius {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    {factor:ℝ} (one:1≤factor) (fare:shift.Budget (Stoop.radius rad factor) P'.p.B (α₁+1) s)  :
    ∃ amplified : Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R,
      (erased).Paid (Stoop.radius rad factor) P'.p.B α₁ r ∧ amplified.Paid (Stoop.radius rad factor) P'.p.B α₁ r ∧
      WilsonOriginalForcedMarkerMerger.Related v (↑((Real.exp (θ*depth))⁻¹):ℂ) erased (actual).K amplified := by
  let target := raised A test H eye rad old hr slots income u tariff apart
  have st := WilsonOriginalForcedMarkerIntake.actual use H Chi.canonical eye.pad M u eye.bells H Ω
    P'.p eye.block eye.pole W.entrance W.offer axis choir toll (occupied A test rad rests) m₁ m₀ target
  have mid := WilsonOriginalForcedMarkerMerger.first _ _ _ st W.first
  have later := WilsonOriginalForcedMarkerMerger.second _ _ _ mid shift W.second
  have prices (l:Trigger.Table A×Bool→ℝ) {τ:ℝ} (m:Motto (brand M u) l 0 H τ K Y eye.sight) :
      (post l m).Paid (Stoop.radius rad factor) P'.p.B α₁ r := by
    have cover := Lanes.layoutK_price H Chi.canonical eye.pad M u l eye.bells m H Ω P'.p eye.block
      eye.pole W.entrance W.offer axis choir toll
    have site := WilsonOriginalForcedMarkerPrice.first (bill l m) W.first hr
      (add_nonneg P'.p.exponent_pos.le zero_le_one) (Hard.mono _ cover eye.room)
    have lower := Stoop.leaves rad _ hr one site
    have final := WilsonOriginalForcedMarkerPrice.second _ shift W.second
      (fun j=>div_pos (hr j) (zero_lt_one.trans_le one)) P'.p.exponent_pos.le lower fare
    exact final
  exact ⟨post fat target,prices del m₀,prices fat target,by
    change Related v (↑((Real.exp (θ*depth))⁻¹):ℂ) (post del m₀) (post base m₁) (post fat target)
    simpa only [Complex.ofReal_inv] using later⟩

theorem original {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    {factor:ℝ} (one:1≤factor) (fare:shift.Budget (Stoop.radius rad factor) P'.p.B (α₁+1) s)  :
    ∃ amplified : Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R,
      (erased).Paid rad P'.p.B α₁ (factor^k*r) ∧ amplified.Paid rad P'.p.B α₁ (factor^k*r) ∧
      WilsonOriginalForcedMarkerMerger.Related v (↑((Real.exp (θ*depth))⁻¹):ℂ) erased (actual).K amplified := by
  obtain ⟨raised,zero,high,line⟩ := at_radius H W eye A rad old hr slots degree income u shift lamp test
    rests tariff apart one fare
  exact ⟨raised,Stoop.budget rad degree _ hr one zero,Stoop.budget rad degree _ hr one high,line⟩

open WilsonOriginalSignedHardHearing
open Comparison.RG02.Order
variable {Fidx:Type*} [Countable Fidx] (E:Lamps α Fidx G P'.p (S.ratio.parent ∘ o) R)

theorem posterior {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    {factor:ℝ} (one:1≤factor) (fare:shift.Budget (Stoop.radius rad factor) P'.p.B (α₁+1) s)
    {estate x₀ x₁ x₂ x₃ x₄:ℝ} (soft:E.Paid rad P'.p.B α₁ estate)
    (law:P'.Lawful x₀ x₁ x₂ x₃ x₄) :
    ∃ raised:Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R,
    (erased).Paid rad P'.p.B α₁ (factor^k*r) ∧ raised.Paid rad P'.p.B α₁ (factor^k*r) ∧
    ∀ t:α,∀ j:R.Mode,∀ n₀:ℕ,
      let mass:ℂ:=(∫ Z:Config G c,P'.eval Z ∂prior G c:ℝ)
      let holding : Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R → Poly R :=
        fun forced=>logTo n₀ (mean (prior G c) mass ((⟨E,forced⟩:Gallery α Fidx _ P' R).density t))
      (holding (actual).K).part j-(holding erased).part j =
        (↑((Real.exp (θ*depth))⁻¹):ℂ)*((holding raised).part j-(holding erased).part j) := by
  obtain ⟨raised,pa,pf,marked⟩:=original H W eye A rad old hr slots degree income u shift lamp test
    rests tariff apart one fare
  refine ⟨raised,pa,pf,?_⟩
  intro t j n₀
  let gal (K:Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R) :
      Gallery α Fidx (S.ratio.parent ∘ o) P' R:=⟨E,K⟩
  have ready (K:Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R)
      (paid:K.Paid rad P'.p.B α₁ (factor^k*r)) (l:R.Mode) :
      Integrable (fun Z=>((gal K).density t Z).part l) (prior G c) :=
    (Poly.get l).integrable_comp (QuadraticLocal.Tariff.integrable R _ rad hr (gal K) t
      (show (gal K).Pays rad α₁ estate (factor^k*r) from ⟨soft,paid⟩) P'.p.exponent_pos.le law)
  apply logged (v:=v) (prior G c) _ ((gal erased).density t) ((gal (actual).K).density t)
    ((gal raised).density t) _ (ready _ pa) (ready _ pf) n₀ j
  intro Z
  exact field erased (actual).K raised marked E pa pf hr t Z

variable {J₂:Type} [Countable J₂]
variable (newborn:Lamps α J₂ G P'.p (S.ratio.parent ∘ o) R)
local notation "full" => WilsonRootedKioskSlipCharge.roll shift newborn
local notation "old0" => without H W eye A rad old hr slots degree income u full test
local notation "entry" => Travel.mid H W eye A rad old hr slots degree income u

theorem issued {v:V} (rests:∀ t:R.Mode,test t→v∈t.val)
    (tariff:Lyric.radiusCost Q L (α₀-θ)) (apart:∀ t:R.Mode,test t→
      ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w))
    {baseFee fee:ℝ} (prior:shift.Budget rad P'.p.B (α₁+1) baseFee)
    (added:WilsonRootedKioskOccupiedSlip.Gross newborn rad P'.p.B (α₁+1) fee) (margin:0<s) (extra:ℝ) :
    let factor:=WilsonRootedKioskFreeRadius.radius extra baseFee fee s
    ∃ amplified : Hard α P'.p P'.activities.forced P'.activities.K (S.ratio.parent ∘ o) R,
      (old0).Paid rad P'.p.B α₁ (factor^k*r) ∧ amplified.Paid rad P'.p.B α₁ (factor^k*r) ∧
      WilsonOriginalForcedMarkerMerger.Related v (↑((Real.exp (θ*depth))⁻¹):ℂ)
        old0 (Kiosk.Second.canopy entry full W.second) amplified := by
  intro factor
  obtain ⟨one,_,price⟩:=WilsonRootedKioskFreeRadius.original shift newborn hr prior added margin extra
  exact original H W eye A rad old hr slots degree income u full newborn test rests tariff apart one price

end YM.Integration.WilsonOriginalRaisedHardPost
end
