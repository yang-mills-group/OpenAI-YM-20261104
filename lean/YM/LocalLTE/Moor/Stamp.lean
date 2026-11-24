import YM.LocalLTE.Moor.Pledge
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Ninety
import YM.LocalLTE.Moor.Windows
/-! Anchors on the virtual and origin Torus. Choose post-L before k-width Directory
for labels (not before momentum posts). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable (G : Gauge) (L : Side)

def resize (ℓ b:ℕ) := ((b+20)*(ℓ+4)^2)*30
lemma studioCmp {R:ℕ}(b ℓ:ℕ)(he:0<R): Meadow.studioN ℓ b R ≤ Meadow.studio (resize ℓ b) R:=by
  unfold Meadow.studioN Meadow.studio Meadow.roomSizeN Meadow.roomSize Mint.width resize
  nlinarith only [show 1 ≤ R from he, Nat.zero_le (b*R*ℓ),Nat.zero_le (b*R*ℓ*ℓ),Nat.zero_le (b*R),Nat.zero_le (R*ℓ), Nat.mul_le_mul_left ℓ (show 1≤R from he),Nat.mul_le_mul_left (ℓ*ℓ) (show 1≤R from he)]
lemma frames_fields (ℓ b:ℕ) (v:ℝ) (hw:-(1/2:ℝ)<v) : ∀ᶠ t in atTop,∀ (P:BudgetPoint), P.threshold ≤ 2*Pressure.fiery G t L →
      let d:=YM.LocalLTE.Inset.cone v (betaF G t L)
      let f:= resize ℓ b; let h:=Trio.base f (radiusB t); let r:= fence f (radiusB t) 
      ∀ c:Side, 2*h<c.val→∀ o:Site c,∀ V: Config G c, Healthy P.threshold (neighbors h o) V→ ∀ i:Stars, ∃ (u:Site (r i)→G.El) (p: Positions (Uniform.Primary (r i) G)), actual p=gauge u (Slide.shape (Trio.pad (w:=tent f (radiusB t)) (fun l:Stars=> (show (r l).val=2*(tent f (radiusB t)+l.val) from rfl)) i) o V) ∧ ‖p‖+2*Sienna.furl G L t<d := by
  let f:= resize ℓ b
  filter_upwards [Trio.summoned G L v hw (fun x=>Trio.base f (radiusB x)) ((Trio.rows G L f).2.2.1.uses)] with t ht P hp
  intro d f h r c hc o V hV i; let v' := tent f (radiusB t)+i.val
  have hz:v'+1 ≤ h:=by change _ ≤ tent f _+5; unfold v'; have hi:= i.isLt; omega
  exact ht P hp c (r i) hc v' hz (le_of_eq rfl) o V hV -- edit
end YM.PhysicalNext.Repeat.Trio
