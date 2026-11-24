import YM.Integration.WilsonMeasuredPublicEntranceOrderedBasis
import YM.Integration.WilsonOriginalBlissMixedGram
/-! The finite reading is the original normalized Wilson reflection pairing. Its continuum value uses the projected physical labels and the reflection adjoint on the left. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOriginalPair
open Filter Finset Lattice Wilson RG Source Labels Cells
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonPositionOriginalDiagnosticMeasuredGram WilsonOriginalBlissSimultaneousGram
open WilsonOriginalBlissMixedGram (grades columns testPair)
open WilsonMeasuredPublicEntranceOrderedBasis
open private tags from YM.Integration.WilsonOriginalBlissMixedGram
open scoped Classical Topology
variable {G:Gauge}(R:Run G){order:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family order S)
  (a:Axis)(d e:ℕ)(φ ψ:Test 1)
  (hp:∀x∈tsupport φ,Points.allAbove a 0 x)(hq:∀x∈tsupport ψ,Points.allAbove a 0 x)

def reading (N p:ℕ)(v:R.family.label d)(w:R.family.label e):ℂ:=
  Cells.form (R.family.beta N p) (plane R.family N p a)
    (stem R.family (oneTest R e a ψ hq w) N p) (stem R.family (oneTest R d a φ hp v) N p)

def named (v:S.Field d)(w:S.Field e):ℂ:=
  (testPair R a d e φ ψ hp hq).applyTo fun x=>S.classMoment S (grades d e) x
    (Fin.cons (α:=fun i=>S.Field (grades d e i)) (S.adj F.room.kernel.spin d a v) (fun _=>w))

def bounds (H J:ℝ):Fin 2→ℝ:=
  Fin.cons (‖(R.family.book.mirrorGroup d (Signed.mirror a)).toContinuousLinearMap‖*H) (fun _=>J)

theorem bounded {H J:ℝ}{v:R.family.label d}{w:R.family.label e}(old:‖v‖≤H)(new:‖w‖≤J):
    ∀i,‖columns R a d e v w i‖≤bounds R a d H J i:=by
  intro i
  fin_cases i
  · let move:=(R.family.book.mirrorGroup d (Signed.mirror a)).toContinuousLinearMap
    change ‖move (star v)‖≤‖move‖*H
    exact (move.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_star v).le.trans old) (norm_nonneg _))
  · exact new

theorem at_cut:
    order.late fun N p=>∀(v:R.family.label d)(w:R.family.label e),
      finiteValue (grades d e) (testPair R a d e φ ψ hp hq) N p (columns R a d e v w)=
        reading R a d e φ ψ hp hq N p v w:=by
  let pred:=fun z:ℕ×ℕ=>∀(v:R.family.label d)(w:R.family.label e),
    finiteValue (grades d e) (testPair R a d e φ ψ hp hq) z.1 z.2 (columns R a d e v w)=
      reading R a d e φ ψ hp hq z.1 z.2 v w
  apply (Order.fused order pred).mp
  have placed:∀ᶠz:ℕ×ℕ in order.fuse,Extraction.suitable R.family.S z.2 φ:=by
    change ∀ᶠp:ℕ in atTop,∀ᶠj:ℕ in atTop,Extraction.suitable R.family.S (order.per p) φ
    filter_upwards [order.per.cofinal.eventually (Extraction.reading R.family.S φ)] with p yes using .of_forall (fun _=>yes)
  filter_upwards [placed,Next.UVStress.large_mesh order (R.family.ref d)] with z place active
  intro v w
  have same:=Extraction.Banks.at_cut R.family (oneTest R d a φ hp v) (oneTest R e a ψ hq w)
    (fun _=>active) place R.makes
  rw [tags] at same
  exact same

theorem projected (v:R.family.label d)(w:R.family.label e):
    publicValue (S:=S) (grades d e) (testPair R a d e φ ψ hp hq) (columns R a d e v w)=
      named R F a d e φ ψ hp hq (S.project d v) (S.project e w):=by
  have same:(fun i=>S.project _ (columns R a d e v w i))=
      Fin.cons (α:=fun i=>S.Field (grades d e i)) (S.adj F.room.kernel.spin d a (S.project d v)) (fun _=>S.project e w):=by
    funext i
    fin_cases i <;> rfl
  simp only [publicValue,named,same]

theorem converges {b:Filter (ℕ×ℕ)}[b.NeBot](below:b≤order.fuse)
    {x:ℕ×ℕ→R.family.label d}{y:ℕ×ℕ→R.family.label e}{v:R.family.label d}{w:R.family.label e}
    (hx:Tendsto x b (𝓝 v))(hy:Tendsto y b (𝓝 w)):
    Tendsto (fun z=>reading R a d e φ ψ hp hq z.1 z.2 (x z) (y z)) b
      (𝓝 (named R F a d e φ ψ hp hq (S.project d v) (S.project e w))):=by
  rw [←projected,←represented F]
  exact WilsonOriginalBlissMixedGram.cutoff R F a d e φ ψ hp hq below hx hy

end YM.Integration.WilsonMeasuredPublicEntranceOriginalPair
end
