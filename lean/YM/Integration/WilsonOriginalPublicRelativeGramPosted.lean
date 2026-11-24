import YM.Integration.WilsonOriginalPublicRelativeGramPrint

/-! On one pair of true public dates the numerical signed receipts are the
ordinary original ear, two independent single-residual ears, and the old scalar
with its remaining two-residual expectation. The upper reference source,
independent quiet, quadrature and kinetic variable are shared throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramPosted
open Filter Finset Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open Source MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicPivotCross (Film detector old)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicRelativeGramPanel (before measured)
open WilsonOriginalPublicRelativeGramJoined (fee)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
private abbrev Cutoff := ℕ×ℕ
variable {G:Gauge}(R:Run G)(W:Initialize G){I L:Type}[Fintype I][Fintype L](d:I→ℕ)

structure Dated where
  nodes:Cutoff→L→Sample 2
  mass:Cutoff→L→ℂ
  q:ℕ
  g:Cutoff→ℝ
  adjoint:Cutoff→(i:I)→(R.family.labels.level (d i)).Coeff
  source:Bool→Cutoff→(i:I)→(R.family.labels.level (d i)).Coeff
  leftBasis:Cutoff→I→Film W
  rightBasis:Cutoff→I→Film W
  frame:Bool→Cutoff→Matrix I I ℂ

variable (sale:Dated (L:=L) R W d)
private abbrev grades (i j:I):Fin 2→ℕ:=WilsonOriginalBlissMixedGram.grades (d i) (d j)
def issued (t:Bool)(z:Cutoff)(i j:I)(k:Fin 2):(R.family.labels.level (grades d i j k)).Coeff:=
  Fin.cons (α:=fun k=>(R.family.labels.level (grades d i j k)).Coeff) (sale.adjoint z i)
    (fun _=>sale.source t z j) k

local notation "H" => fun z=>detector W (sale.nodes z) (sale.mass z) sale.q (sale.g z)
local notation "v" => issued R W d sale
local notation "x" => fun z i k=>sale.frame false z k i
local notation "y" => fun t z j k=>sale.frame t z k j

def submitted (t:Bool)(z:Cutoff)(i j:I):ℂ:=
  sampled R W (grades d i j) (v t z i j) (sale.nodes z) (sale.mass z) univ sale.q (sale.g z)

def gram (z:Cutoff):Matrix I I ℂ:=fun i j=>(H z) (sale.leftBasis z i*sale.rightBasis z j)

def deposits (t:Bool)(z:Cutoff)(i j:I):ℝ:=
  let U:=WilsonOriginalPublicPivotCross.left R W (grades d i j) (v t z i j) (x z i) (sale.leftBasis z)
  let V:=WilsonOriginalPublicPivotCross.right R W (grades d i j) (v t z i j) (y t z j) (sale.rightBasis z)
  ‖∑k,star (x z i k)*(H z) (sale.leftBasis z k*V)‖+
    ‖∑k,y t z j k*(H z) (U*sale.rightBasis z k)‖+
    ‖old R W (grades d i j) (v t z i j) (sale.nodes z) (sale.mass z) sale.q (sale.g z)+(H z) (U*V)‖

theorem printed (t:Bool)(z:Cutoff)(i j:I):
    ‖submitted R W d sale t z i j-
      ((sale.frame false z)ᴴ*gram R W d sale z*sale.frame t z) i j‖ ≤ deposits R W d sale t z i j:=by
  rw [←WilsonOriginalPublicRelativeGramPrint.entry]
  exact WilsonOriginalPublicRelativeGramPrint.priced R W (grades d i j) (v t z i j)
    (sale.nodes z) (sale.mass z) sale.q (sale.g z) (x z i) (y t z j) (sale.leftBasis z) (sale.rightBasis z)
    _ _ _ le_rfl le_rfl le_rfl

variable [DecidableEq I]{f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {Hc:(Climb.Bel R.family.book).Hierarchy}{ℓ:Ultrafilter Cutoff}
  (arch:Trace.Terrace.Arch R.family)(bliss:Trace.Pilot.Bliss F ℓ arch Hc)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)(shift:∀k,ℝ→R.family.label k ≃ₗ[ℂ] R.family.label k)
  (a:Axis)(w:(i:I)→(Spin.comparator R.family.book).Field (d i))(φ:I→Test 1)
  (supports:∀i,∀p∈tsupport (φ i),Points.allAbove a 0 p)
local notation "O" => before R F arch J level shift a d w φ
local notation "M" => measured R J a d w φ supports

include bliss in
theorem original (r s:ℝ)(atR:∀i,R.family.ref (d i) ≤ level r)(atS:∀i,R.family.ref (d i) ≤ level s)
    (tuition rest:Bool→I→I→ℝ)(η:ℝ)(ep:0<η)
    (earned:∀ᶠ z:Cutoff in f.fuse,∀t i j,
      ‖O r (cond t s r) z i j-submitted R W d sale t z i j‖ ≤ tuition t i j ∧
       deposits R W d sale t z i j ≤ rest t i j)
    (rank:IsUnit (M r r).det)(small:‖(M r r)⁻¹‖*fee η (tuition false+rest false) ≤ 1/2):
    ∀ᶠ z:Cutoff in (ℓ:Filter Cutoff),IsUnit (sale.frame false z).det ∧
      ‖(M r r)⁻¹*M r s-(sale.frame false z)⁻¹*sale.frame true z‖ ≤
        2*‖(M r r)⁻¹‖*(fee η (tuition true+rest true)+fee η (tuition false+rest false)*‖(M r r)⁻¹*M r s‖):=by
  apply WilsonOriginalPublicRelativeGramJoined.original R F arch bliss J level shift a d w φ supports
    r s atR atS (sale.frame false) (sale.frame true) (gram R W d sale) _ _ η ep _ rank small
  filter_upwards [earned] with z hz
  have each(t:Bool)(i j:I):
      ‖O r (cond t s r) z i j-((sale.frame false z)ᴴ*gram R W d sale z*sale.frame t z) i j‖ ≤
        tuition t i j+rest t i j:=by
    calc
      _ ≤ ‖O r (cond t s r) z i j-submitted R W d sale t z i j‖+
        ‖submitted R W d sale t z i j-((sale.frame false z)ᴴ*gram R W d sale z*sale.frame t z) i j‖ := by
          simpa only [dist_eq_norm] using dist_triangle (O r (cond t s r) z i j)
            (submitted R W d sale t z i j) (((sale.frame false z)ᴴ*gram R W d sale z*sale.frame t z) i j)
      _ ≤ _ := add_le_add (hz t i j).1 ((printed R W d sale t z i j).trans (hz t i j).2)
  exact fun i j=>⟨each false i j,each true i j⟩

end YM.Integration.WilsonOriginalPublicRelativeGramPosted
