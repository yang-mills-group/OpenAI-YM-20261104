import YM.Frontier.Tuning.BarHol
import YM.Frontier.Tuning.MeristemC
import YM.Frontier.Tuning.JetHol
import YM.Frontier.Tuning.HolColor
import YM.Frontier.Tuning.RecoilIdentity
import YM.Frontier.Tuning.WingC
import YM.Frontier.Tuning.ZestPalette
import YM.Frontier.Tuning.CarryC

/-! Actual integration bounds before period by combining postperiod neighborhood domination with pointwise angular estimates (later). No gluing of masks varying with the draw. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Frontier.Tuning.ContourGerm
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Blaze Art Silica Poll Pond Eider Flux Held GlassLog Zest TwoMotion RecoilIdentity Shield DensityTilt PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]{x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {η Y r' Q' W : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Q:ConnectedActivityE6.Target G P} {R R': Rep G f}
variable (hP : Port P L η r' Q' Y X)
variable (ho : Intake P T X.x R) (ht:Facing R R')(hr:Intake P T X.x R')
variable (J : Finset (Bond f)) {K K' : ℝ} (hK:Canary G K K')(z':Molecule S)
variable {μ S0 C'':ℝ}{o:Target.Order G W}(H0: Cash W S0 μ L Q o C'' T R)
open Set Metric Complex
structure Box (U:Set ℂ)(g:E→ℂ→ℂ)(y:E)(j:ℕ) : Prop where
 funds : ∃ B, ∀ᶠ x' in 𝓝 y,∀ w∈U, Brush j B 1 (fun y=>g y w) x' ∧ DifferentiableAt ℂ (g x') w
section
variable {S':Set ℂ}{g:E→ℂ→ℂ}
lemma pocket (U : Set ℂ)(g:E→ℂ→ℂ)(hS:IsCompact S')(hs:S'⊆U)(hp:∀ w∈U, ∃ (B:ℝ) (T':Set E) (_ht:T'∈𝓝 x) (S:Set ℂ) (_hS:S ∈ 𝓝 w),
      ∀ y∈T',∀ q∈S,Brush j B 1 (fun y=>g y q) y ∧ DifferentiableAt ℂ (g y) q) : Box S' g x j :=by
  let R:Filter (ℝ×E):= atTop ×ˢ (𝓝 x)
  let Q(q:ℂ) (y:ℝ×E):Prop:= Brush j y.1 1 (fun y=> g y q) y.2 ∧ DifferentiableAt ℂ (g y.2) q
  have he w (hw:w∈U) : ∀ᶠ y in (𝓝 w) ×ˢ R, Q y.1 y.2:= by
     obtain ⟨B,V,hV,W,hW,hQ⟩:=hp w hw
     filter_upwards [show ∀ᶠ y in (𝓝 w)×ˢ R, y∈W×ˢ (Ici B×ˢ V) from prod_mem_prod hW (prod_mem_prod (Ici_mem_atTop _) hV)] with y hy; exact ⟨(hQ y.2.2 hy.2.2 y.1 hy.1).1.climb hy.2.1 le_rfl,(hQ _ hy.2.2 _ hy.1).2⟩
  replace he:∀ᶠ y in (𝓝ˢ S')×ˢ R,Q y.1 y.2:=hS.mem_nhdsSet_prod_of_forall fun i hi=>he i (hs hi)
  have hR : (atTop : Filter ℝ).NeBot:= inferInstance
  rw [Filter.eventually_prod_iff] at he
  obtain ⟨W,hW,V,hV,hQ⟩:=he
  obtain ⟨B,hp⟩:=(show ∀ᶠ y in R,V y from hV).curry.exists
  refine ⟨B,hp.mono fun x hx q hq=>?_⟩
  exact hQ (subset_of_mem_nhdsSet (t:=W) hW hq) hx
end
local notation "pbar" => edgesM S (H0.unionP z') (radiusB X.x)
variable (hX: X.width=o.K) (hS:X.x = S0) (he : 8*o.a*X.t ≤ K/2) (U : Set ℂ) (τ:ℂ→ℂ)(e'f h:ℂ→Payload G f) (hU:IsOpen U)(hτ:DifferentiableOn ℂ τ U) {bM:ℝ}
   (hb : ∀ i∈U,0<(τ i).re ∧ fans R R' bM (e'f i) (h i))(_he : ∀ n y,DifferentiableOn ℂ (fun z=>e'f z n y) U)(hh : ∀ n y,DifferentiableOn ℂ (fun z=>h z n y) U)
include H ht hr hP hK H0 hX hS he hU hτ hb _he hh
lemma local_bounds {S':Set ℂ}(hS':IsCompact S')(hs:S'⊆U):
    let g y i := barC pbar R (e'f i) (h i) (vary X (C y)) Q.table o.a W Q.halo z' (τ i)
    Box S' g x j:=by
   intro g; refine pocket U g hS' hs fun w hw=>?_
   obtain ⟨b,hb,T,h₁,S,h₂,v,hS0,hTS,hI,h3,h4,h5⟩:=BarHol.local_bounds H hP ht hr hK z' H0 hX hS he U τ e'f h hU hτ hb _he hh w hw
   refine ⟨b,T,h₁,S,h₂,fun t ht q hq=>⟨?_,(h3 t ht).differentiableAt (hS0.mem_nhds hq)⟩⟩
   have hh:=(h5 q hq t ht).1.buds v hI zero_le_one (h5 q hq t ht).2.1 (ae_of_all _ (h5 q hq t ht).2.2)
   apply hh.shimmy
   exact (show ∀ᶠ t' in 𝓝 t,t'∈T from hTS.mem_nhds ht).mono (fun t' ht'=> (h4 t' ht' q hq))
end YM.Frontier.Tuning.ContourGerm
