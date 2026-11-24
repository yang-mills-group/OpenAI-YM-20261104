import YM.Integration.WilsonOriginalPublicRelativeGramWeakHeads
import YM.Integration.WilsonOriginalTwoFlatPublicBooks

/-! The raw pooled and weak measuring labels for the signed finite reflected
comparison come from the same enrolled original public book on its opening. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramBookedHeads
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonOriginalPublicRelativeGramReflectedLimit (ordered entered)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits gram)
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramWeakHeads (cofile)
variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(room:ℝ→Prop)
    {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}
    (cap:h≤D)(books:(r:ℝ) → room r → WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) H arch D T r)
private abbrev seat:Fin (D+1):=⟨h,Nat.lt_succ_of_le cap⟩
local notation "P" i:max => named R B h i

def source (branch:Bool)(r:ℝ)(z:ℕ×ℕ)(i:Glyph B h):R.family.label h:=by
  classical
  exact if hr:room r then ((((books r hr).rows (seat h cap)).arm branch (J r h (P i))).source z) else 0

def label (branch:Bool)(r:ℝ)(i:Glyph B h):R.family.label h:=by
  classical
  exact if hr:room r then ((((books r hr).rows (seat h cap)).arm branch (J r h (P i))).label) else 0

theorem appointed (branch:Bool)(active:∀ᶠr in trail,room r):
    ∀ᶠr in trail,(∀i,Tendsto (fun z=>source B h R F J ℓ room cap books branch r z i)
        (ℓ:Filter (ℕ×ℕ)) (𝓝 (label B h R F J ℓ room cap books branch r i))) ∧
      ∀i,S.project h (label B h R F J ℓ room cap books branch r i)=J r h (P i):=by
  filter_upwards [active] with r hr
  constructor <;> intro i
  · simpa only [source,label,dif_pos hr,seat] using
      (((books r hr).rows (seat h cap)).arm branch (J r h (P i))).approaches
  · simpa only [label,dif_pos hr,seat] using
      (((books r hr).rows (seat h cap)).arm branch (J r h (P i))).represents

section Return
variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "I" => Glyph B h
local notation "Z" => ℝ×(ℕ×ℕ)
local notation "d" => (fun _:I=>h)
local notation "fused" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (room:ℝ→Prop)(active:∀ᶠr in trail,room r)
    {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}(cap:h≤D)
    (books:(r:ℝ) → room r → WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) H arch D T r)
    (W:Initialize G)(sale:ℝ→Dated (L:=Unit) R W d)(fee:Z→I→I→ℝ)(level:I→ℕ)
    (wide:ℝ→Dated (L:=Unit) R W d)(ε:Z→ℝ)
    (covered:Tendsto (fun p:Z=>gram R W d (sale p.1) p.2) fused (𝓝 (maxwell B h a)))
    (hearing:∀ i j,∀ᶠp:Z in fused,
      ‖entered B h a R F ℓ avoid Γ (source B h R F J ℓ room cap books false) p i j-submitted R W d (sale p.1) false p.2 i j‖≤fee p i j)
    (fresh:∀ i j,Tendsto (fun p:Z=>fee p i j) fused (𝓝 0))
    (deposited:∀ i j,Tendsto (fun p:Z=>deposits R W d (sale p.1) false p.2 i j) fused (𝓝 0))
    (relative:∀ᶠp:Z in fused,
      let row:=cofile (sale p.1) (wide p.1)
      IsUnit (row.frame false p.2).det ∧ ‖(1:Matrix I I ℂ)-(row.frame false p.2)⁻¹*row.frame true p.2‖≤ε p)
    (rate:Tendsto ε fused (𝓝 0))
    (heads:∀i j,level j≤level i → Tendsto (fun p:Z=>(wide p.1).frame true p.2 i j) fused
      (𝓝 ((1:Matrix I I ℂ) i j))):
    Tendsto (fun p:Z=>(sale p.1).frame false p.2) fused (𝓝 1) ∧
    Tendsto (fun p:Z=>(wide p.1).frame true p.2) fused (𝓝 1):=by
  exact WilsonOriginalPublicRelativeGramWeakHeads.original B h a R F J ℓ avoid Γ simple temperature
    lead below _ _ (appointed B h R F J ℓ room cap books false active) W sale fee level wide ε
    covered hearing fresh deposited relative rate heads
end Return
end YM.Integration.WilsonOriginalPublicRelativeGramBookedHeads
