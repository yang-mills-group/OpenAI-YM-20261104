import YM.Integration.WilsonPositionSeparatedProfileMayerWickWord

/-! A registered stencil has a finite selection of original free-link color
coordinates, independently of the period. Conditioning on a forest may
identify two of these coordinates or set one to zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerStencilSites
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series
variable {I:Type} [Fintype I] (run:Run G) (d:I→ℕ)
abbrev Letter:=Σ i:I,Source.UsedEdges (run.family.localSection (d i)).stencil × G.ColorIndex

omit [Fintype I] in
def slots:(Letter run d→ℝ)→ₗ[ℝ]Panels run d where
  toFun a i l:=WithLp.toLp 2 fun c=>a ⟨i,l,c⟩
  map_add' a b:=by funext i l;apply PiLp.ext;intro c;rfl
  map_smul' t a:=by funext i l;apply PiLp.ext;intro c;rfl

variable (X:Coat T F) (loc:I→Site f)
def link (k:Letter run d):Bond f:=(wrap f k.2.1.val.1+loc k.1,k.2.1.val.2)
def filed (k:Letter run d):Option (Eye X):=if h:link run d loc k∈F.trunks then none else
    some (Native.lineEquiv (G:=G) F X.x (⟨link run d loc k,h⟩,k.2.2))

omit [Fintype I] in
theorem placed (z:Air f G):slots run d (fun k=>(filed run d X loc k).elim 0 fun j=>z (tube X j))=restrict run d F loc z:=by
  funext i l;apply PiLp.ext;intro a
  let e:Bond f:=(wrap f l.val.1+loc i,l.val.2)
  change ((if h:e∈F.trunks then none else some (Native.lineEquiv (G:=G) F X.x (⟨e,h⟩,a))).elim 0 (fun j=>z (tube X j)))=(WilsonCoherentMayerNoise.row F z e).ofLp a
  by_cases he:e∈F.trunks <;> simp only [he,dif_pos,Option.elim_none,WilsonCoherentMayerNoise.row,if_true,if_false] <;> rfl

variable {A B:Type}
def wires (tags:A→Option B) (i:A):B→₀ℂ:=(tags i).elim 0 (fun j=>Finsupp.single j 1)

theorem pay (tags:A→Option B) (p:Normal.poly A):Rise.coin (Normal.exchange (wires tags) p)≤Rise.coin p:=by
  have each:∀i,Rise.cents (Normal.glyph (wires tags i)) 0 (1:ℝ)≤1:=by
    intro i;cases h:tags i <;> simp [wires,h,Normal.glyph,Finsupp.linearCombination_single,Rise.pay_X]
  simpa only [one_pow,mul_one] using Rise.rise (wires tags) 0 zero_le_one (le_refl 1) each p (le_refl _)

theorem read (tags:A→Option B) (z:B→ℝ) (p:Normal.poly A):Cloud.paint z (Normal.exchange (wires tags) p)=Cloud.paint (fun i=>(tags i).elim 0 z) p:=by
  unfold Cloud.paint;rw [Normal.reads_val];apply congrArg (fun q:A→ℂ=>MvPolynomial.aeval q p)
  funext i;cases h:tags i <;> simp [wires,Normal.reads,h]

end YM.Integration.WilsonPositionSeparatedProfileMayerStencilSites
