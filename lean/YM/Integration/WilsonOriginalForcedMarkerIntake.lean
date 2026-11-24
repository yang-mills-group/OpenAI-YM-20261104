import YM.Integration.WilsonOriginalForcedMarkerRows

/-! Put the original countable signed scenes in the very forced arrays
used by the elected first and second merger. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalForcedMarkerIntake
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse
open RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe QuadraticLocal QuadraticLocal.Lanes
open WilsonOriginalHardOwnerReweight WilsonForcedMarkerLine WilsonOriginalForcedMarkerMerger
open WilsonOriginalForcedMarkerRows
open scoped Topology BigOperators Classical

variable {V ι : Type} [DecidableEq V] [Countable ι] {R : Marker.Census V} {v : V}
    {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G}
    {T : Tube G S} {A : Rep G f} {W x μ C τ τ' θ a d e K σ Y γ Gp ε :ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {α:Type*}
    {J k s n j depth:ℕ}
variable (use:ι→Prop) (H : Cash W x μ L Q o C T A) (χ : Chi) (U:Pad H j χ)
    (M : ι → Portrait A α) (u:α) (h:Roles H χ U k s J n a d e K σ Y γ Gp ε)
    {A' : Rep G f} (H' : Cash W x μ L Q o C T A') (D : Match.Alliance H' H 1 0)
    (out:BudgetPoint) (hw:out.B=radiusB x) (ht:out.threshold=Pressure.temp x)
    (E : ℕ → RegularAddress c) (b : ℕ → Config G c → ℝ)
    {root:V→Site c} (z:ι→Poly R) {g:V→ℝ} (choir:Chorus R g Set.univ z k)
    (hc:∀ i,Corrected.Width.LocalCharge (G:=G) out root (Flues.candle M u S i) (fun _=>z i))

local notation "base" => (fun _ : ι=>(1:ℝ))
local notation "del" => omitOwner use
local notation "fat" => raise use θ depth
local notation "mm" t:max v:max => Motto (brand M u) t 0 H v K Y n
local notation "firm" t:max hT:max => Lanes.layoutK H χ U M u t h hT H' D out hw ht E b z choir hc
local notation "sample" t:max => Lanes.shaft H χ U M u t H' D out ht E b z hc

theorem actual (marker : ∀ i,use i → pinned v (z i))
    (live : mm base τ) (clipped : mm del τ) (boost : mm fat τ') :
    Related v (↑(Real.exp (θ*depth)):ℂ)⁻¹ (firm del clipped) (firm base live) (firm fat boost) := by
  intro y i Z
  have covered (l:ι→ℝ) {q:ℝ} (m:mm l q) := Lanes.shaftPrice H χ U M u l h m H' D out hw ht E b z choir hc
  have s₀ := (covered del clipped).quality (sample del) h.price.visit.posts choir.votes Z y i
  have s₂ := (covered fat boost).quality (sample fat) h.price.visit.posts choir.votes Z y i
  apply WilsonOriginalForcedMarkerRows.rows _ s₀ s₂
  intro index
  exact WilsonOriginalForcedMarkerRows.signed use z H χ M u H' D E b marker y index.val Z

end YM.Integration.WilsonOriginalForcedMarkerIntake
end
