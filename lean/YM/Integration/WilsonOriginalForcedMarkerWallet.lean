import YM.Integration.WilsonOriginalSeparatedHardReturn
import YM.Integration.WilsonOriginalForcedMarkerPrice

/-! Purchase the three catalogs on the same original cash and the actual
support of the selected occupied forced address. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalForcedMarkerWallet
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger
open WilsonOriginalHardOwnerReweight WilsonOriginalHardOwnerSuccessor
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.AbsoluteSums Pressure
open Push.SectorMeasure ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Lotus Merge
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse
open RemainderComparison.Mosaic QuadraticLocal WilsonOriginalForcedMarkerRows
open scoped Topology BigOperators Classical
variable {ι E:Type} [Fintype E] {G:Gauge} {n c:Side} {S:StepData c n}
    {P:Rep G n} {leaf:ι→Lotus.Leaf P} {root:E→Site n} {source:ι→Finset E}
    {a b:ℝ} {N:ℕ}

theorem clipped (h:Scale root source leaf (fun _=>1) N a b S) (use:ι→Prop) :
    Scale root source leaf (omitOwner use) N a b S := by
  have lo i : 0≤omitOwner use i := by unfold omitOwner; split <;> norm_num
  have hi i : omitOwner use i ≤ 1 := by unfold omitOwner; split <;> norm_num
  refine ⟨lo,?_,?_,h.tolerance,h.sizes⟩
  · intro i hp
    apply h.pin i
    simpa only [Palette.wages,one_mul] using (pos_of_mul_pos_right hp (lo i))
  · intro y
    refine Extra.Multi.Budget.mono (h.crown y) ?_ ?_ le_rfl
    · intro i; split
      · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (lo i) (leaf i).profit)
      · exact le_rfl
    · intro i; split_ifs
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hi i) (leaf i).profit) (Real.exp_pos _).le
      · exact le_rfl

variable {w x κ b' z e f r s Γ Y K:ℝ} {L:Side} {D:Tube G S} {C:Teller G}
    {Q:ConnectedActivityE6.Target G C} {h:ConnectedActivityE6.Target.Order G w}
    {P':Rep G c} {α : Type*} {I V : Type} [DecidableEq V] [Countable I]
    {R:Marker.Census V} {o:V→Site n} {k depth:ℕ}
variable (A:Gallery α I o P R) (test:R.Mode→Prop) (H:Cash w x κ L Q h z D P)
    (eye:Travel.Eyes H P' e Γ Y K k) (rad:V→ℝ) (old:Travel.Seal A rad b b')
    (hr:∀v,0<rad v) (slots:HasSlots P.p P.activities) (income:2*(b+b')≤K) (u:α)
local notation "raw" => Trigger.listCosts A rad hr slots old.supE old.crown (Travel.sighting A rad old) old.looks
local notation "S₀" => brand raw u
local notation "base" => (fun _:Trigger.Table A×Bool=>(1:ℝ))
local notation "use" => WilsonOriginalSeparatedHardReturn.owned A test
local notation "α₁" => P.p.supportExponent
local notation "θ" => P.p.supportExponent/8

include income in
theorem omitted : Motto S₀ (omitOwner use) 0 H α₁ K Y eye.sight := by
  have bank:=Travel.fiscal H eye A rad old hr slots income u
  obtain ⟨carrier,cf,addresses,rows,cap⟩:=bank.claim
  letI:Fintype carrier:=cf
  exact ⟨⟨carrier,cf,addresses,rows,clipped cap use⟩,bank.target,le_rfl,by simp,by simp⟩

include income in
theorem raised (tariff:radiusCost Q L (α₁-θ)) (wide:∀ t:R.Mode,test t→
    ∃v∈t.val,∃w∈t.val,depth*(4*P.p.B+2)+2*P.p.B ≤ separation (o v) (o w)) :
    Motto S₀ (WilsonOriginalHardOwnerReweight.raise use θ depth) 0 H (α₁-θ) K Y eye.sight := by
  have bank:=Travel.fiscal H eye A rad old hr slots income u
  obtain ⟨carrier,cf,addresses,rows,cap⟩:=bank.claim
  letI:Fintype carrier:=cf
  have pos:0≤θ := div_nonneg P.p.exponent_pos.le (by norm_num)
  have paid:=WilsonOriginalHardOwnerReweight.scale cap pos use
    (WilsonOriginalSeparatedHardReturn.covered A test rad old hr slots u wide)
  exact ⟨⟨carrier,cf,addresses,rows,paid⟩,tariff,le_rfl,by simp,by simp⟩

omit [Countable I] in
theorem occupied {v:V} (root:∀ t:R.Mode,test t→v∈t.val) :
    ∀i,use i→WilsonForcedMarkerLine.pinned v (Trigger.axis A rad i) := by
  rintro ⟨j|j,parity⟩ hit
  · exact False.elim hit
  · intro m hm
    have root' := root j.val.2 hit
    have diff : j.val.2 ≠ m := fun he=>hm (he ▸ root')
    simp [Trigger.axis,Trigger.status,Poly.part_send,Ne.symm diff]

end YM.Integration.WilsonOriginalForcedMarkerWallet
end
