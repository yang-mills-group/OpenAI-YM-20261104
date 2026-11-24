import YM.Integration.WilsonOriginalPublicRelativeGramNativeMeasure
import YM.Integration.WilsonOriginalPublicRelativeGramNativeCeiling

/-! The actual finite reflected source and independently prescribed group
matrix at their common optical ruler. The bound is selected before the collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeSalary
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus Pert.Asymptotics
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits gram)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered)
open WilsonOriginalPublicRelativeGramNativePivot (Ruler filed)
open WilsonOriginalPublicRelativeGramNativeMeasure (beam)
open WilsonOriginalPublicRelativeGramNativeCeiling (Adequate)
open WilsonPositionProgramTrialOpticalBand (Bracket)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(B:Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ → tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ → ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g) (pres:WilsonPrescription G)(L:Ruler R pres.run)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
local notation "fused" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))
local notation "Book" => Dated (L:=Unit) R pres.scheme d

theorem original {C:ℝ}(room:Adequate B h a C){simple:G.Simple}(temperature:Coupling G g)
    (lead:Leading F J)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    {M₀:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(verified:Main.Match pres simple M₀ T dial)
    {A:ℝ}(ap:0≤A)(cut:Bracket R L.cut A)
    (Y:ℝ → (ℕ×ℕ) → Glyph B h → R.family.label h)(b:ℝ → Glyph B h → R.family.label h)
    (selected:∀ᶠs in trail,(∀i:Glyph B h,Tendsto (fun z=>Y s z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b s i))) ∧
      ∀i:Glyph B h,S.project h (b s i)=J s h (named R B h i))
    (site:∀ᶠr in trail,L.place r=Γ.date (L.scale r))
    (paper:ℝ → Book)(q:ℕ)(fee:Z → I → I → ℝ)
    (hearing:∀i j,∀ᶠp:Z in fused,‖beam B h a R pres.run avoid L Y p i j-
      submitted R pres.scheme d (filed R pres B h a avoid L q p.1 (paper p.1)) false p.2 i j‖≤fee p i j)
    (fresh:∀i j,Tendsto (fun p:Z=>fee p i j) fused (𝓝 0))
    (deposited:∀i j,Tendsto (fun p:Z=>
      deposits R pres.scheme d (filed R pres B h a avoid L q p.1 (paper p.1)) false p.2 i j) fused (𝓝 0)):
    ∀ᶠp:Z in fused,‖(filed R pres B h a avoid L q p.1 (paper p.1)).frame false p.2‖≤C:=by
  let sale:=fun r=>filed R pres B h a avoid L q r (paper r)
  let pool:=fun p:Z=>(sale p.1).frame false p.2
  let H:=fun p:Z=>gram R pres.scheme d (sale p.1) p.2
  let M:=maxwell B h a
  let P:=beam B h a R pres.run avoid L Y
  have physical:Tendsto P fused (𝓝 M):=WilsonOriginalPublicRelativeGramNativeMeasure.original
    B h a R pres.run F J ℓ avoid Γ L Y simple temperature lead below b selected site
  have covered:Tendsto H fused (𝓝 M):=WilsonOriginalPublicRelativeGramNativePivot.original
    R pres B h a avoid L ℓ paper q verified below ap cut
  have self:Tendsto (fun p:Z=>(pool p)ᴴ*H p*pool p) fused (𝓝 M):=by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have near:Tendsto (fun p:Z=>P p i j) fused (𝓝 (M i j)):=
      ((continuous_id.matrix_elem i j).tendsto _).comp physical
    have difference:Tendsto (fun p:Z=>P p i j-((pool p)ᴴ*H p*pool p) i j) fused (𝓝 0):=by
      refine squeeze_zero_norm' ?_ (show Tendsto (fun p:Z=>fee p i j+deposits R pres.scheme d (sale p.1) false p.2 i j) fused (𝓝 0) from ?_)
      · filter_upwards [hearing i j] with p price
        exact (norm_sub_le_norm_sub_add_norm_sub _ (submitted R pres.scheme d (sale p.1) false p.2 i j) _).trans
          (add_le_add price (WilsonOriginalPublicRelativeGramPosted.printed R pres.scheme d (sale p.1) false p.2 i j))
      · simpa only [add_zero] using (fresh i j).add (deposited i j)
    simpa only [sub_sub_cancel,sub_zero] using near.sub difference
  exact room pool H covered self

end YM.Integration.WilsonOriginalPublicRelativeGramNativeSalary
