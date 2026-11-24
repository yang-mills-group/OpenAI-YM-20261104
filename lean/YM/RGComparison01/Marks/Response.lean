import YM.RGComparison01.Marks.Heron
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Response
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion Next.Scheduling
variable [Fintype ι]
variable (M:ι→Lotus.Leaf R)(g:ι→ℝ)
variable (V:Config G c){κ:Type}
-- Same mechanism as Photo.acts without exponential form of A being normalized/preReset.Output
-- pre-exponent abstract as positive for now. `Oc` sums are ACTUAL.
variable (f₀:ℝ) (hq: 0<f₀) (V':Activities G c)(P':BudgetPoint) (K':ℝ→Finset ι → Code G c)
variable (T':κ→ Ways ι) {u:κ→ℝ}(hp: ∀ i,Paid (fun _:Unit=>T' i) (u i)) (ht:Summable u)
include H
open Marker GridRenewal.Rain
lemma phoenix {B:Type}[Fintype B][DecidableEq B](E:Marker.Census B)(f:ι→Marker.Poly E)(hf : ∀ i,f i*f i=0)(hE:∀ i,(f i).part E.quiet=0)
    (hc : ∀ i p,T' i 0 p=0) (hv:Motion.Pays V' P' K' w P'.supportExponent) (hx:∀ x:ℝ,x∈ Set.Icc 0 1 → ∀ p,f₀*Real.exp (∑' i,T' i x p)*(black V' (K' x p)).gas P' V=S.push R.beta (Palette.buy M (Palette.ways g x p) S) V)
    (hp: ∀ i,Paid (fun _:Unit=>T' i) (u i)) (ht:Summable u):
    S.push R.beta (Photo.given (S:=S) M g E f) V= (f₀:ℂ) • (Marker.Poly.pass (∑' i,sound f (T' i))*∑' p,Photo.fronts V' (fun i=>sound f (fun t p=>K' t p i V)) V P' p):= by
   let Bf:Ways ι:=fun t p=> ∑' i,T' i t p
   have hh : HasSum (fun i=>sound f (T' i)) (sound f Bf):= soundSum f T' hp ht (fun _ _ _=>rfl)
   have hB : Paid (fun _:Unit=>Bf) (∑' i,u i):= (Switch.issue hp ht).1
   have h0 : (sound f Bf).part E.quiet=0:=by rw [Switch.sunset (fun _:Unit=>Bf) hB f () hE]; unfold Bf; simp only [hc,tsum_zero,Complex.ofReal_zero]
   let Y: Ways ι:=fun t p => Real.exp (Bf t p); let U:Ways ι:=fun _ _=> f₀
   let t i (u:ℝ)(p:Finset ι):= Photo.tomes (P:=P') V' K' i V u p
   let Z : Ways ι:=fun s p=> ∑' i,t i s p
   obtain ⟨b,hb,hC⟩:= Photo.tomes_budget _ _ hv;
   have hZ: Paid (fun _:Unit=>Z) (∑' i,b i) := (Switch.issue (fun i=>show Paid (fun _:Unit=> t i) _ from (hC i).toPoint _ V) hb).1
   have hv' : Paid (fun _:Unit=>U) ‖f₀‖:=Switch.constant _ (norm_nonneg _) (fun _=>le_rfl)
   rw [Photo.which M H, hh.tsum_eq, (Photo.holds f hf V' K' hv V).tsum_eq, ← GridRenewal.Rain.passes (sound f Bf) h0]
   change sound f _= (↑f₀:ℂ) • (cyclone (sound f Bf)*sound f Z)
   rw [← show sound f (U*(Y*Z))= sound f (fun t p=> S.push R.beta (Palette.buy M (Palette.ways g t p) S) V) from congr_arg (mapScores E f) (Switch.cong (Switch.approached.mono fun i hi=> funext fun j => (by rw [← hx _ ⟨hi.1.le,hi.2⟩ j]; change f₀*(_* _) = f₀ *_* Z i j; ring))) ]
   have hY:Paid (fun _:Unit=>Y) _:=hB.exponential
   rw [mul_sounds f hf (show Models U _ from (hv'.works ()).choose_spec) (show Models (Y*Z) _ from ((hY.mul hZ).works ()).choose_spec),mul_sounds f hf (show Models Y _ from (hY.works ()).choose_spec) (show Models Z _ from (hZ.works ()).choose_spec), show sound f Y= _ from soundExp f hf hB,const_sounds,Poly.product_bead]
end Response
end YM.RGComparison01.Pledge
