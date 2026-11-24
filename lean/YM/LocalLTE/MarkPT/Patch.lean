import YM.LocalLTE.MarkPT.Pulses
/-! Orbit-shared explicit mark proposal. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
-- parity.Y allele tall cone factor.Deferred.B.Gouge.
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')
variable (Φ:ℕ→ℝ→ Config G f→ℝ)(Ψ:ι→ℝ→ Config G f→ℝ)
open Weft
-- actual peg gives lens equality with overprescribed Φ$.
variable (hΦ:∀ i,r₀ i≤ n→ R.activities.E i=Φ i (gStep R.beta))
variable (hΨ:∀ i,A' i→ Ψ i (gStep R.beta)=φ i)
local notation "B₀"=> (gStep R.beta)
include hx hΦ hΨ
lemma pint (m:ℕ)(i:Option (Fin z.fst))(x:Disk G c): pinPT M H χ Φ Ψ (z.2 i) (D i) m B₀ x=pinV M φ H χ (z.2 i) (D i) m x:=by -- cap lowercase
    let X(r:Reserve S)(k:S.Choices):= ((prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL k); let v:=z.2 i; let J:=fibers H v; let W:=quietR M v (D i)
    have he (r:Reserve S)(k:S.Choices): Fan.wishPT (L:=L) (o:=o) (t:=t) M Q (D i) (X r k) (W) J m Φ Ψ B₀ x= Fan.wishes (L:=L) (o:=o) M φ Q (D i) (X r k) W J t m x:=by
       let X:= X r k; let R':= Fan.vest R Φ B₀
       have hx' : R'.beta=R.beta:=by unfold R'; change ((gStep R.beta)^2)⁻¹=_; rw [gStep, inv_pow,inv_inv,Real.sq_sqrt H.laws.intake.positive.le]
       have hh (i':Veil c f) (hi:i'∈W) y: Fan.coming Q.table R' X x y i'=Fan.coming Q.table R X x y i':=by
           unfold Fan.coming; rw [hx']; rcases i' with i'|i'
           · exact congr_arg (fun f:Config G f→ℝ=> - f (inputΛ X y x)) (hΦ _ (hx.loans i' i hi)).symm
           rfl
       unfold wishPT wishes; refine MeasureTheory.integral_congr_ae (ae_of_all _ fun y=> ?_)
       unfold calPT; apply congr_arg (pledgeΛ X J y (Vine.pass x)* ·); apply congr_arg₂ (·*·); exact prod_congr rfl fun j hj=> congr_fun (hΨ j (hx.petals i j hj)) _ -- syntax
       exact prod_congr rfl fun i hi=> congr_arg (Bakers.afloat m) (hh i hi (Pond.spill J y))
    exact congr_arg likely (funext fun r:Reserve S=>congr_arg likely (funext fun k:S.Choices=> he r k)) -- likely infer
lemma gleams (m k h:ℕ){u:Site c} (X:Grove u)(κ:ℝ)(hp:2*(2*h)≤ c.val): lensPT M H χ z D Φ Ψ m k h X κ hp B₀= Fan.lenses M φ H χ z D m k h X κ hp:=by
    let F:=Fold.trace u h hp (G:=G)
    have he: Fan.micaPT M H χ z D Φ Ψ m B₀= Fan.mica M φ H χ z D m:=by funext x; exact prod_congr rfl fun i _=> Fan.pint M φ H χ z D q n r₀ A' hx Φ Ψ hΦ hΨ m i x
    have hh:Fan.twirlPT M H χ z D Φ Ψ m k F B₀= Fan.twirled M φ H χ z D m k F:= by unfold Fan.twirlPT Fan.twirled Fan.forecasts; rw [he]
    unfold Fan.lensPT Fan.lenses Fan.boat; rw [hh]
-- oversight `lensPT(s)` with V only depends petals.PNE. Need P.Prohib fit unaffected.Arbitrary.Later.
end YM.LocalLTE.Fan
