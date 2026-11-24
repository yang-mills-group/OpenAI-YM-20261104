import YM.RGComparison01.Marks.Reels
import YM.RGComparison01.Marks.Luggage
import YM.RGComparison01.Sluice
/-!
# Coastline estimates for marked portfolio aggregate

 Uncentered (includes constants REQUIRED by denominator). Leverages the
 generic `Shore` lemma with centering and separately bound constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Oceanic
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion
open Push.Uniform Sienna Fare Lapis Boulevard Next.Scheduling Further.LogJets
-- cert at sunny using true H display `f=H+W`. Need bound H(0)
variable (P':BudgetPoint) (A:ℕ→ RegularAddress c)(u:ℕ → Config G c→ℝ) (F H : Config G c→ℝ)
-- R remains before turnFee. both paths positive orientation.Mark LOG. Width.h rule allows zero bound separately.
variable {b : ℝ}
variable (he:P'.order=j)(hK:P'.threshold=Pressure.temp t) (hp:P'.threshold ≤ 2*Pressure.fiery G t L) (hg: Sluice.Shore G L j t r)
  (h : Meadow.Budget P' A u b) -- b binder
local notation "Z"=> Positions (Uniform.Primary c G)
include hp hK he hg h
lemma clasp (U : Z)(hU:‖U‖+2*Sienna.furl G L t<r)(ht: flags P'.threshold (actual U)=∅)
   (hF:P'.Regular univ H) (hc:∀ V:Config G c,V∈ Boulevard.sunny P' → F V=H V + Boulevard.throng u V)
   (hV:∀ W:Positions (Uniform.Primary c G),‖W‖+2*Sienna.furl G L t<r → actual W∈sunny P' → Brush j v r⁻¹ (F∘ Boulevard.actual) W):
   ∀ l:List (Directions G c),l.length ≤ P'.order→ (∀ i∈l,‖i‖≤P'.threshold)→ ‖leftDerivs H l (actual U)‖ ≤ (Boulevard.ticket j (v+v) + 2*((Fintype.card (Site c):ℝ)*b)) + (v + (Fintype.card (Site c):ℝ)*b):= by
   have hy:‖(0:Z)‖+2*Sienna.furl G L t<r:= by have h:=norm_nonneg U; rw [norm_zero]; linarith
   have hx: (1:Config G c)∈ sunny P':= Pencils.blue P'
   have hv₀ : ‖F 1‖≤v:=by simpa only [Function.comp_apply, Pencils.created] using (hV 0 hy (Pencils.created.symm ▸ hx)).bound
   let b':=(Fintype.card (Site c):ℝ)*b
   have hh : ‖H 1‖≤v+b':= by rw [show H 1=F 1- Boulevard.throng u 1 from (hc 1 hx ▸ (add_sub_cancel_right ..)).symm]; exact (norm_sub_le ..).trans (add_le_add hv₀ ((Boulevard.commemorates h 1 hx).2 [] (by simp) (by simp)))
   -- convert to old Shore with f = - F and unchanged H&u
   let f':=fun x:Config G c=> - F x
   have H'(V:Config G c)(he:V∈ sunny P'): f' V=0-H V-Boulevard.throng u V:= by unfold f'; rw [hc V he]; ring
   intro l hl hs
   have hR:= hg P' he hK hp U hU ht A u H f' (v+v) b 0 h hF H' ?_ l hl hs
   swap
   · intro V hv hw
     have h := hV V hv hw
     refine ((Brush.certified h.pos (F 1)).climb hv₀ le_rfl|>.separating h).shimmy (Eventually.of_forall fun x=> ?_)
     unfold stillA Function.comp f'; ring
   let t:= actual U
   let V' := fun _: Config G c=> H 1
   have hg:H= (Boulevard.stillA H)-((-1:ℝ) • V'):= by ext i; simp [V',Boulevard.stillA]
   have hz: Healthy P'.threshold (Finset.univ) (actual U):= by unfold Healthy; rw [ht]; simp
   have hX : Push.Local.Chart P'.order V' t:= contDiffAt_const
   have hY := CouplingShape.reg_sub hF (CouplingShape.reg_const (X:=univ) (H 1))
   have hV₀:(-1:ℝ) • V' = (fun _=>- H 1):= by ext i; simp [V']
   nth_rw 1 [hg]; rw [hV₀]; rw [VerifiedReset.left_sub (g:=fun _=> -H 1) (hY.smooth _ hz) (f:=Boulevard.stillA H) (show Push.Local.Chart P'.order (fun (_:Config G c)=> -H 1) (actual U) from contDiffAt_const) hl]; refine (norm_sub_le ..).trans (add_le_add hR (le_trans ?_ hh))
   cases l <;> simp [Work.G07.left_const, leftDerivs]
-- rounded up for health costs_ geometry
end Oceanic
end YM.RGComparison01.Pledge
