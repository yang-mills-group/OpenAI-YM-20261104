import YM.Integration.WilsonRegisteredHeightIntake

/-! Normalize an occupied measured occurrence by its own genuine support
cost. A zero-cost occurrence vanishes on every field. The original
perturbative diagram bound can therefore be applied before summing the
prices of the actual source terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredMarkedOffer
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical


open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open WilsonInheritedRegisteredField RGLocalTaylor.Mayer PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums ManuscriptQLocalMarkedHeightRun

variable {V I:Type} [DecidableEq V] [Fintype V] [Fintype I] {Γ:Marker.Census V}
variable {G:Gauge} {n:Side} (Y:Rep G n)

def mass (b:Leaf Y):ℝ:=Y.p.mass b.crest b.weight

theorem nonnegative (b:Leaf Y):0 ≤ mass Y b:=mul_nonneg (Real.exp_pos _).le b.profit

def hat (D:ℝ) (b:Leaf Y) (s:Γ.Mode) (occupied:s.val.Nonempty):Menu.Hat Γ Y where
  M:=b
  s:=s
  shiny:=occupied
  charge:=(((D*mass Y b)⁻¹:ℝ):ℂ)

omit [Fintype V] in
theorem original {D:ℝ} (hD:0<D) (b:Leaf Y) (s:Γ.Mode) (occupied:s.val.Nonempty)
    (U:Config G n):
    ((D*mass Y b:ℝ):ℂ)*(hat Y D b s occupied).charge*
      ((hat Y D b s occupied).M.ingredient U:ℂ)=(b.ingredient U:ℂ):=by
  by_cases zero:mass Y b=0
  · have z:b.weight=0:=(mul_eq_zero.mp zero).resolve_left (Real.exp_pos _).ne'
    have earn:=b.earn U
    rw [z,norm_le_zero_iff] at earn
    simp [hat,earn]
  · have nz:D*mass Y b≠0:=mul_ne_zero hD.ne' zero
    change ((D*mass Y b:ℝ):ℂ)*(((D*mass Y b)⁻¹:ℝ):ℂ)*(b.ingredient U:ℂ)=_
    rw [←Complex.ofReal_mul,mul_inv_cancel₀ nz,Complex.ofReal_one,one_mul]

omit [Fintype V] in
theorem fare {D:ℝ} (hD:0<D) (b:Leaf Y) (s:Γ.Mode) (occupied:s.val.Nonempty):
    Menu.fare (hat Y D b s occupied) (fun _=>1)*
      Real.exp (Y.p.supportExponent*coverNumber Y.p.B b.crest)≤D⁻¹:=by
  let m:=mass Y b
  have m0:0 ≤ m:=nonnegative Y b
  have value:Menu.fare (hat Y D b s occupied) (fun _=>1)=(D*m)⁻¹*b.weight:=by
    simp [Menu.fare,Menu.sumFee,Marker.Poly.toll,hat,Complex.norm_real,Real.norm_eq_abs,m,abs_of_nonneg (nonnegative Y b),abs_of_pos hD]
  rw [value]
  calc (D*m)⁻¹*b.weight*Real.exp (Y.p.supportExponent*coverNumber Y.p.B b.crest)=D⁻¹*(m⁻¹*m):=by
         simp only [_root_.mul_inv_rev];change m⁻¹*D⁻¹*b.weight*_ = D⁻¹*(m⁻¹*((Real.exp _)*b.weight));ring
       _ ≤ D⁻¹:=by
         by_cases z:m=0
         · simp [z,hD.le]
         · simp [z]

omit [Fintype V] in
theorem offered {D:ℝ} (hD:0<D) (origin:V→Site n) (b:I→Leaf Y)
    (s:I→Γ.Mode) (occupied:∀i,(s i).val.Nonempty)
    (root:∀i,(s i).val.image origin⊆(b i).crest):
    Menu.Offer origin (fun i=>hat Y D (b i) (s i) (occupied i)) (fun _=>1)
      Y.p.B Y.p.supportExponent (Fintype.card I*D⁻¹):=by
  refine ⟨root,fun u=>?_⟩
  let bill:=fun i:I=>if u∈(b i).crest then
    Menu.fare (hat Y D (b i) (s i) (occupied i)) (fun _=>1)*Real.exp
      (Y.p.supportExponent*coverNumber Y.p.B (b i).crest) else 0
  have pos (i:I):0≤bill i:=by
    dsimp only [bill];split_ifs
    · exact mul_nonneg (Menu.Crew (fun _=>1) (fun _=>one_pos)) (Real.exp_pos _).le
    · exact le_rfl
  have atMost (i:I):bill i≤D⁻¹:=by
    dsimp only [bill];split_ifs
    · exact fare Y hD (b i) (s i) (occupied i)
    · exact (inv_pos.mpr hD).le
  refine ⟨pos,hasSum_fintype bill |>.summable,?_⟩
  rw [tsum_fintype]
  calc _ ≤ ∑_i:I,D⁻¹:=Finset.sum_le_sum fun i _=>atMost i
       _ = _:=by simp

end YM.Integration.WilsonRegisteredMarkedOffer
