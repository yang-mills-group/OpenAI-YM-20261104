import YM.Integration.WilsonOriginalPublicRelativeGramReference
import YM.OPE.Cards.Pressure

/-! Take the two true public panels at a common finite set of original grid
points. Each upper cutoff uses the site's actual deterministic ancestor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramPins
open Filter Finset Function Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open WilsonOriginalBlissMixedGram (grades columns)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {ℓ:Ultrafilter (ℕ×ℕ)}{I L:Type}[Fintype I][Fintype L]
  (a:Axis)(d:I→ℕ)(J:ℝ→PhysMS.tower S)(w:(i:I)→(Spin.comparator R.family.book).Field (d i))
  (r s:ℝ)(site:ℕ)(addresses:L→Fin 2→ Cover)(μ:L→ℂ)
  (Y:Bool→(ℕ×ℕ)→(i:I)→R.family.label (d i))

def physical (t:Bool)(z:ℕ×ℕ)(i j:I)(m:L):ℂ:=
  R.family.ensemble (grades (d i) (d j))
    (fun k=>Cells.location R.family.S site z.1 z.2 (addresses m k))
    (columns R a (d i) (d j) (Y false z i) (Y t z j))

def readings (t:Bool)(i j:I)(m:L):ℂ:=
  S.classMoment S (grades (d i) (d j)) (Extraction.Order.grid R.family site (addresses m))
    (Fin.cons (α:=fun k=>S.Field (grades (d i) (d j) k))
      (S.adj F.room.kernel.spin (d i) a (J r (d i) (w i))) (fun _=>J (cond t s r) (d j) (w j)))

def matrix (t:Bool):Matrix I I ℂ:=fun i j=>∑m,μ m*readings R F a d J w r s site addresses t i j m

def cutoff (t:Bool)(z:ℕ×ℕ):Matrix I I ℂ:=fun i j=>∑m,μ m*physical R a d site addresses Y t z i j m

omit [Fintype I] in
theorem limit (b:Bool→(i:I)→R.family.label (d i))(converges:∀t i,
    Tendsto (fun z=>Y t z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b t i)))
    (same:∀t i,S.project (d i) (b t i)=J (cond t s r) (d i) (w i))
    (below:(ℓ:Filter (ℕ×ℕ)) ≤ f.fuse)
    (admitted:∀m,μ m≠0→Extraction.Order.grid R.family site (addresses m) ∈ generic 2)
    (t:Bool)(i j:I):
    Tendsto (fun z=>cutoff R a d site addresses μ Y t z i j) (ℓ:Filter (ℕ×ℕ))
      (𝓝 (matrix R F a d J w r s site addresses μ t i j)):=by
  unfold cutoff matrix
  apply tendsto_finsetSum
  intro m _
  by_cases zero:μ m=0
  · simpa only [zero,zero_mul] using (tendsto_const_nhds (x:=(0:ℂ)) (f:=(ℓ:Filter (ℕ×ℕ))))
  apply Tendsto.const_mul
  have genericSite:=admitted m zero
  let doses:=columns R a (d i) (d j) (b false i) (b t j)
  let doseAt:=fun z=>columns R a (d i) (d j) (Y false z i) (Y t z j)
  have cv:∀k,Tendsto (fun z=>doseAt z k) (ℓ:Filter (ℕ×ℕ)) (𝓝 (doses k)):=by
    intro k; fin_cases k
    · change Tendsto (fun z=>(R.family.book.mirrorGroup (d i) (Signed.mirror a)) (star (Y false z i))) _ _
      exact (R.family.book.mirrorGroup (d i) _).continuous_of_finiteDimensional.continuousAt.tendsto.comp
        (converges false i).star
    · exact converges t j
  have grid:=Cards.variation (C:=R.family) (d:=grades (d i) (d j)) (addresses m) F.room.generic
    genericSite doses doseAt cv below
  have eq:(fun k=>S.project _ (doses k))=
      Fin.cons (α:=fun k=>S.Field (grades (d i) (d j) k))
        (S.adj F.room.kernel.spin (d i) a (J r (d i) (w i))) (fun _=>J (cond t s r) (d j) (w j)):=by
    funext k; fin_cases k
    · change S.project (d i) (R.family.book.adj (d i) a (b false i))=_
      rw [←S.adj_project F.room.kernel.spin,same false i]
      rfl
    · exact same t j
  have projected:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _:ℕ=>le_rfl)
    (grades (d i) (d j)) (generic_conf 2 genericSite) doses
  change Tendsto _ _ (𝓝 (S.classMoment S _ _ _))
  rw [←eq,projected]
  exact grid

end YM.Integration.WilsonOriginalPublicRelativeGramPins
