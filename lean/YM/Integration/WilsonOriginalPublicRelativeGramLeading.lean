import YM.Integration.WilsonOriginalPublicRelativeGramTransport

/-! Generic true addresses may approach a reflected shape for the leading
reference Gram. Its rank is tested after the original continuum limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramLeading
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks Spec Table Table.Pairing Climb
open PhysMS (MaxwellSlots WickGoal Leading measured)
open WilsonOriginalBlissMixedGram (grades)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {I L Z:Type}[Fintype I][Fintype L]{l:Filter Z}(a:Axis)(d:I→ℕ)(J:ℝ→PhysMS.tower S)
  (w:(i:I)→(Spin.comparator R.family.book).Field (d i))

def fields (i j:I):MaxwellSlots R.family (grades (d i) (d j)):=
  Fin.cons (α:=fun k=>(Spin.comparator R.family.book).Field (grades (d i) (d j) k))
    ((Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) (d i) a (w i)) (fun _=>w j)

variable (r:Z→ℝ)(site:Z→ℕ)(addresses:Z→L→Fin 2→ Cover)(weight:Z→L→ℂ)
    (shape:Z→L→Points 2)(limit:L→Points 2)(μ:L→ℂ)

def free:Matrix I I ℂ:=fun i j=>∑m,μ m*WickGoal (fields R a d w i j) (limit m)

omit [Fintype I] in
theorem original (lead:Leading F J)(small:Tendsto r l (𝓝[>] (0:ℝ)))
    (placed:∀ᶠ z in l,∀m,Extraction.Order.grid R.family (site z) (addresses z m)=r z • shape z m)
    (position:∀m,Tendsto (fun z=>shape z m) l (𝓝 (limit m)))(clear:∀m,limit m∈conf 2)
    (mass:∀m,Tendsto (fun z=>weight z m) l (𝓝 (μ m)))(i j:I):
    Tendsto (fun z=>matrix R F a d J w (r z) (r z) (site z) (addresses z) (weight z) false i j) l
      (𝓝 (free R a d w limit μ i j)):=by
  unfold matrix free
  apply tendsto_finsetSum
  intro m _
  apply (mass m).mul
  have wick:=PhysMS.leading_at F lead (fields R a d w i j) small (position m) (clear m)
  apply wick.congr'
  filter_upwards [placed,small.eventually (lead.equivariant (d i))] with z seats eq
  rw [show readings R F a d J w (r z) (r z) (site z) (addresses z) false i j m=
      S.classMoment S (grades (d i) (d j)) (r z • shape z m)
      (Fin.cons (α:=fun k=>S.Field (grades (d i) (d j) k))
      (S.adj F.room.kernel.spin (d i) a (J (r z) (d i) (w i))) (fun _=>J (r z) (d j) (w j))) by
      simp [readings,seats]]
  unfold measured
  congr 1
  funext k
  fin_cases k
  · change J (r z) (d i) ((Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) _ a (w i))=
      S.adj F.room.kernel.spin (d i) a (J (r z) (d i) (w i))
    change J (r z) (d i) (((Spin.comparator R.family.book).mirror (Maxwell.Free.spin_free R.family.labels) (d i) (Signed.mirror a))
      ((Spin.comparator R.family.book).conj (Maxwell.Free.spin_free R.family.labels) (d i) (w i)))=
      S.mirror F.room.kernel.spin (d i) (Signed.mirror a) (S.conj F.room.kernel.spin (d i) (J (r z) (d i) (w i)))
    rw [eq.1,eq.2]
  · rfl

end YM.Integration.WilsonOriginalPublicRelativeGramLeading
