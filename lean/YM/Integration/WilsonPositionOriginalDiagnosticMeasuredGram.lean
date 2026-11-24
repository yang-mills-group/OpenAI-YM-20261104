import YM.Extraction.Pairs
import YM.Integration.WilsonPositionOriginalDiagnosticReflectedTest

/-! The full reflected Gram of a dressed moving original cutoff column.  The
cut is the fixed reflection plane, and the ordered physical reading is that
of the same real reference radius and signed label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticMeasuredGram
open Function Filter Set Finset MeasureTheory Lattice Wilson Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Order Extraction.Banks
open Spec Table Table.Pairing RG17
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
  (F:Spec.Final R.family f S)(L:Layout F)
local notation "C"=>R.family

def oneTest (d:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x)(w:R.family.label d):
    Table.PastTest R.family.book a:=⟨1,fun _=>⟨d,w⟩,φ,ok⟩

def smear (d:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x)
    (rr:ℝ)(v:R.family.label d)(N per:ℕ):Config G (R.family.side N per) → ℂ:=
  stem C (oneTest R d a φ ok (atRef L d rr (N,per) v)) N per

def doubled (d:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x):Test 2:=
  withOther (oneTest R d a φ ok 0) (oneTest R d a φ ok 0)

def two (d:ℕ)(a:Axis)(v:R.family.label d):Fin 2 → R.family.label d:=
  Fin.cons (R.family.book.adj d a v) (fun _=>v)

private theorem labels (d:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x)(v:R.family.label d):
    let V:=oneTest R d a φ ok v
    tied V.v V.v a=fun i=>(⟨d,two R d a v i⟩:R.family.book.Token):=by
  dsimp only
  funext i
  fin_cases i <;> rfl

theorem original (d:ℕ)(a:Axis)(φ:Test 1)(ok:∀x∈tsupport φ,Points.allAbove a 0 x)
    (rr:ℝ)(v:R.family.label d)(age:R.family.ref d≤L.level rr)
    (l:Filter (ℕ×ℕ))[l.NeBot](inside:l≤L.lens):
    Tendsto (fun i:ℕ×ℕ=>let X:=smear R F L d a φ ok rr v i.1 i.2
      Cells.form (R.family.beta i.1 i.2) (plane C i.1 i.2 a) X X)
      l (𝓝 (S.integralOn (fun _:Fin 2=>d) (two R d a (locatedRef L d rr v)) (doubled R d a φ ok))):=by
  let x(i:ℕ×ℕ):=atRef L d rr i v
  let V(i:ℕ×ℕ):=oneTest R d a φ ok (x i)
  have tend:Tendsto x l (𝓝 (locatedRef L d rr v)):=tendsRef L inside tendsto_const_nhds age
  have adj:Tendsto (fun i=>(R.family.book.adj d a) (x i)) l (𝓝 ((R.family.book.adj d a) (locatedRef L d rr v))):=by
    change Tendsto (fun i=>(R.family.book.mirrorGroup d (Signed.mirror a)) (star (x i))) l _
    exact (R.family.book.mirrorGroup d _).continuous_of_finiteDimensional.continuousAt.tendsto.comp tend.star
  have buy:=Next.UVStress.calibrated_smear F.room.ordered l (inside.trans L.certified) (doubled R d a φ ok)
    (d:=fun _:Fin 2=>d) (v:=fun i=>two R d a (x i)) (x:=two R d a (locatedRef L d rr v))
    (he:=by intro j;fin_cases j;exact adj;exact tend)
  have read:∀ᶠi:ℕ×ℕ in f.fuse, suitable R.family.S i.2 φ:=by
    change ∀ᶠp:ℕ in atTop, ∀ᶠ j:ℕ in atTop, suitable R.family.S (f.per p) φ
    filter_upwards [f.per.cofinal.eventually (reading R.family.S φ)] with p hp using Eventually.of_forall (fun _=>hp)
  apply buy.congr'
  filter_upwards [read.filter_mono (inside.trans L.certified),(Next.UVStress.large_mesh f (R.family.ref d)).filter_mono (inside.trans L.certified)]
    with i safe late
  have same:=at_cut C (V i) (V i) (fun _=>late) safe R.makes
  rw [labels R d a φ ok] at same
  exact same

end YM.Integration.WilsonPositionOriginalDiagnosticMeasuredGram
