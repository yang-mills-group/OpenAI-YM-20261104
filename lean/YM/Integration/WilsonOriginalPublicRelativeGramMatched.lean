import YM.Integration.WilsonOriginalPublicRelativeGramPlanted

/-! Two genuinely filed public arms are calibrated on the finite independent
Wilson pivot fields and the original two physical reflected panels. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramMatched
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered entered)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits gram)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

open XSpace.Cirrus FVA2 FVA2.Register
open WilsonPositionProgramPublicReflectedRead (lower)
open WilsonOriginalPublicRelativeGramBookedHeads (source)
open WilsonOriginalPublicRelativeGramWeakHeads (cofile)
open WilsonOriginalPublicRelativeGramPlanted (file)
variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
local notation "fused" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

variable (pres:WilsonPrescription G){sg:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T₀:Prescription (Press.portDeck G)}{dial:Bool}(verified:Main.Match pres sg M T₀ dial)
local notation "W" => pres.scheme

include verified in
theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (room:ℝ→Prop)(active:∀ᶠr in trail,room r)
    {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}(cap:h≤D)
    (books:(r:ℝ) → room r → WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) H arch D T r)
    (sale:ℝ → Dated (L:=Unit) R W d)(q₀:ℕ)(date:ℝ→ℕ)(fee:Z→I→I→ℝ)(level:I→ℕ)
    (wide:ℝ → Dated (L:=Unit) R W d)(ε:Z→ℝ)
    {t:ℝ→ℝ}(positive:∀ᶠr in trail,0<t r)(small:Tendsto t trail (𝓝 0))
    (lo hi:ℝ)(lp:0<lo)(span:∀ᶠr in trail,
      lo*(-Real.log (t r))≤ -Real.log (pres.run.step (date r)).spacing ∧
      -Real.log (pres.run.step (date r)).spacing≤hi*(-Real.log (t r)))
    (near:Tendsto (fun p:Z=>familiar ((sale p.1).nodes p.2 ())) fused (𝓝 (lower a)))
    (samples:∀ᶠp:Z in fused,((sale p.1).nodes p.2 ()).F=pres.run.step (date p.1) ∧
      welcome ((sale p.1).nodes p.2 ()) ∧ (sale p.1).mass p.2 ()=1 ∧ |(sale p.1).g p.2|≤8*t p.1)
    (hearing:∀ i j,∀ᶠp:Z in fused,
      ‖entered B h a R F ℓ avoid Γ (source B h R F J ℓ room cap books false) p i j-submitted R W d (file pres B h a R (sale p.1) q₀ (date p.1)) false p.2 i j‖≤fee p i j)
    (fresh:∀ i j,Tendsto (fun p:Z=>fee p i j) fused (𝓝 0))
    (deposited:∀ i j,Tendsto (fun p:Z=>deposits R W d (file pres B h a R (sale p.1) q₀ (date p.1)) false p.2 i j) fused (𝓝 0))
    (relative:∀ᶠp:Z in fused,
      let row:=cofile (file pres B h a R (sale p.1) q₀ (date p.1)) (file pres B h a R (wide p.1) q₀ (date p.1))
      IsUnit (row.frame false p.2).det ∧ ‖(1:Matrix I I ℂ)-(row.frame false p.2)⁻¹*row.frame true p.2‖≤ε p)
    (rate:Tendsto ε fused (𝓝 0))
    (heads:∀i j,level j≤level i → Tendsto (fun p:Z=>(wide p.1).frame true p.2 i j) fused
      (𝓝 ((1:Matrix I I ℂ) i j))):
    Tendsto (fun p:Z=>(sale p.1).frame false p.2) fused (𝓝 1) ∧
    Tendsto (fun p:Z=>(wide p.1).frame true p.2) fused (𝓝 1):=by
  exact WilsonOriginalPublicRelativeGramBookedHeads.original B h a R F J ℓ avoid Γ simple temperature
    lead below room active cap books W (fun r=>file pres B h a R (sale r) q₀ (date r)) fee level
    (fun r=>file pres B h a R (wide r) q₀ (date r)) ε
    (WilsonOriginalPublicRelativeGramPlanted.original pres B h a R ℓ sale q₀ date verified
      positive small lo hi lp span near samples)
    hearing fresh deposited relative rate heads

end YM.Integration.WilsonOriginalPublicRelativeGramMatched
