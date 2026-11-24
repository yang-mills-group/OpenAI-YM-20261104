import YM.LocalTaylorR2.Capstone.Corral
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir
/-!
 # Marquee budget even when anchor is not transferred by Alliance. Allocate directly.
 `hit_panel` is crucial - a theorem only proving equality of total density or even
 regular anchored-posting error in the contour before the transfer along figure-H won't
 show this budget. Cost unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Capstone
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}

open YM.RG01.Survive
variable {v ρ w δ β a : ℝ}{j K n M : ℕ}{ℓ : ℝ}{g : Expansions H M}{x : H.ThinP→Orders M→ℝ}{z : H.ThinP→ℝ}
    (h:ReadyAll χ g v j x z ρ) (X:Match.Alliance I H 1 0) (γ : ℝ)
include h
variable (p:BudgetPoint)
    (hs:p.threshold=Pressure.temp s)(hp:p.B=radiusB s)(hi:p.order≤j)(n:ℕ)(hn:p.power≤n)
    (q:ℝ)(hq:0≤q)(hS:Sailor G p.threshold q j)(hr:j*q≤v)(hv:0<v)
    (hA: Quotes.preExponent p ≤ a)(hδ:0<δ)(hY:Ready H.smallAt p.B (fun i=>2^j*z i) (a+δ) w δ β)

include hs hp hi hn hq hS hr hv hA hδ hY

lemma guarded (take:ℕ→Prop) (r:ℕ) (he:∀ i,take i → r ≤ i) :
    let u:=cohort H (χ:=χ) X γ g false take
    let s:= RG01.Survive.readerCost (G:=G) p j n ρ δ s w β r
    Meadow.Budget p (Beam.marquee I p).reg u.logRead s:=by
  have hf:= h.hit_panel (H:=H) (fun _ i => take i) p w δ β a hs hp hi n hn q hq hS hr hv hA hδ hY r (fun _=>he)
  intro A t
  let f i:= (ρ^r)⁻¹*LeafReady.allowance p i j n z
  let k:Magazine I →ℝ:=Sum.elim (fun i=>f (X.furrow i)) (fun _=>0)
  let W i:=(-1:ℝ) • fullSegments (fun _ q => take q) g (X.furrow i)
  let V:Magazine I → Config G c→ℝ:=Sum.elim W (fun _=>0)
  have hW : A.logRead= choir V ∘ pennant I:= by unfold A cohort V; dsimp only; simp [W]
  rw [hW]; apply Meadow.soared
  have hy (z) := h.germs (χ:=χ) (fun _ i=>take i) (X.furrow z) p hs hi hp q hq hS hr hv n hn (Beam.dashboard I z).site (show (Beam.dashboard I z).site∈Song.perf H (X.furrow z) from by rw [← Song.reconnects I X z, ← Beam.see I z]; exact (Beam.dashboard I z).anchor) r he
    (fun i=> nonneg_of_mul_nonneg_right (hY.2.2.2.2.1 i) (by positivity : (0:ℝ)<2^j))
  have hX (m:Magazine I):p.Regular (Beam.contents I p m).support (V m)∧p.supBounds (Beam.contents I p m).site (Beam.contents I p m).support (V m) (k m):=by
    rcases m with m|m
    · have hh:= (hy m).2
      have hs: (Beam.contents I p (.inl m)).support=reachability (X.furrow m):= (Beam.see I _).trans (reconnects I X _)
      rw [hs]; exact ⟨CouplingShape.reg_scale _ (hy m).1,by simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) hh⟩
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(Beam.contents I p (.inr m)).support) (o:=(Beam.contents I p (.inr m)).site) 0)⟩

  refine ⟨k,fun i=> ?_,hX⟩
  set a:ℝ:=(ρ^r)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹))
  rw [← add_zero a]; apply Cost.sum
  · let M j := Beam.dashboard I j
    refine budget_mono (Cost.equiv X.furrow (hf i)) ?_ ?_
    · intro i; dsimp only; split
      next=>exact mul_nonneg ((hX (.inl i)).2.1) (Real.exp_pos _).le
      exact le_rfl
    intro j
    let z:=X.furrow j
    change (if (M j).site=i then _ else _)≤ if i∈reachability z then _ else _
    have hg : (M j).support=reachability z:= (Beam.see I _).trans (Song.reconnects I X _)
    split
    next hp0=>
      rw [if_pos (show i∈ reachability z from hg ▸ hp0 ▸ (M j).anchor)]; change f z*Real.exp (preExponent p * coverNumber _ (M j).support)≤_
      rw [hg]
    exact (hf i).1 z
  simp [SumBudget,k]
end YM.LocalTaylorR2.Capstone
