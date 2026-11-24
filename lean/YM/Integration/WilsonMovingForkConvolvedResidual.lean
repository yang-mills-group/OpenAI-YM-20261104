import YM.Integration.WilsonMovingForkPooledRows
import YM.Integration.WilsonMovingForkSameExterior

/-! The same finite exterior fit acts on the already convolved full-minus-columns
scalar. Its count and fee have no dependence on the two original regulators. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkConvolvedResidual
open Function Filter Finset MeasureTheory Extraction Table Spec RG17 OPE OPE.Orbits Lattice Wilson Climb
open PhysicalNext.Repeat.Legato WilsonOriginalTwoFlatPublicBooks WilsonThermometerUnitFilingFourSquare
open WilsonMovingForkPooledRows (arms)
open WilsonPublicForkPooledHearing (markedCut)
open scoped Classical BigOperators Topology

theorem finite {I B:Type}[Fintype I][Fintype B]
    (c:B→ℂ)(w:I→ℂ)(Y:ℂ)(M:B→ℂ)(y:I→ℂ)(m:I→B→ℂ)(e:ℝ)(fees:B→ℝ)
    (full:‖Y-∑i,w i*y i‖≤e)(columns:∀k,‖M k-∑i,w i*m i k‖≤fees k):
    ‖Y-∑k,c k*M k‖≤(e+∑k,‖c k‖*fees k)+∑i,‖w i‖*‖y i-∑k,c k*m i k‖:=by
  classical
  have swap:∑k,(c k*(∑i,w i*m i k))=∑i,(w i*(∑k,c k*m i k)):=by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _=>sum_congr rfl fun k _=>by ring
  have diff:Y-∑k,c k*M k=(Y-∑i,w i*y i)-
      (∑k,c k*(M k-∑i,w i*m i k))+(∑i,w i*(y i-∑k,c k*m i k)):=by
    simp_rw [mul_sub]
    rw [sum_sub_distrib,sum_sub_distrib,swap]
    abel
  have ncols:‖∑k,c k*(M k-∑i,w i*m i k)‖≤∑k,‖c k‖*fees k:=
    (norm_sum_le _ _).trans (sum_le_sum fun k _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (columns k) (norm_nonneg _))
  have nrows:‖∑i,w i*(y i-∑k,c k*m i k)‖≤∑i,‖w i‖*‖y i-∑k,c k*m i k‖:=by
    apply (norm_sum_le _ _).trans_eq;apply sum_congr rfl;intro i hi;rw [norm_mul]
  rw [diff]
  exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le ..).trans (add_le_add full ncols)) nrows)

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=ℓ) H z D T s.val)
local notation "C" => R.family
local notation "Date" => {s:ℝ //0<s ∧ s<δ}

theorem original (order:(ℓ:Filter _)≤f.fuse){n h:ℕ}{d:Caps n}{B:Type}[Fintype B]
    (near:Labels S d)(out:B→S.Field h)(X:External C S)(r t:Date)(ψ:Test n)
    (covered:packs X r.val ψ)(income:Integrable (fun u:Points (X.n+1)=>X.test u*query F near (X.offset u) X.labels none r.val ψ))
    (dnear:∀i,d i<D+1)(dout:h<D+1)(dx:∀j,(X.tags j).1<D+1)
    (branch:Fin n→Bool)(column:B→Bool):
    let all:=Fin.append (tags near) X.tags
    let two:=fun k=>Fin.cons (α:=fun _=>S.Tag) ⟨h,out k⟩ X.tags
    ∃wholeCaps:∀i,(all i).1<D+1,∃gramCaps:∀k i,((two k) i).1<D+1,
    let Y:=markedCut all (arms F books all wholeCaps (Fin.append (fun _:Fin n=>r) (fun _:Fin X.n=>t))
      (Fin.append branch (fun _:Fin X.n=>false))) (shape X r.val ψ)
    let M:=fun k=>markedCut (two k) (arms F books (two k) (gramCaps k) (Fin.cons r (fun _:Fin X.n=>t))
      (Fin.cons (column k) (fun _:Fin X.n=>false))) X.test
    ∀{I:Type},∀[Fintype I],∀c:B→ℂ,∀w:(ℕ×ℕ)→I→ℂ,∀y:(ℕ×ℕ)→I→ℂ,∀m:(ℕ×ℕ)→I→B→ℂ,
    ∀e:ℝ,∀fees:B→ℝ,∀tail home:ℝ,0≤tail→
    (∃ᶠk in (ℓ:Filter (ℕ×ℕ)),
      ‖Y k-∑i,w k i*y k i‖≤e ∧ (∀b,‖M b k-∑i,w k i*m k i b‖≤fees b) ∧
      (∑i,‖w k i‖)≤home ∧ ∀i,‖y k i-∑b,c b*m k i b‖≤tail)→
    ‖appeared F near X r.val ψ-∑b,c b*X.charge F h (out b)‖≤(e+∑b,‖c b‖*fees b)+home*tail:=by
  classical
  intro all two
  obtain ⟨wc,gc,full,gram⟩:=WilsonMovingForkPooledRows.original F books order near out X r t ψ covered income
    dnear dout dx branch column (fun _=>false)
  refine ⟨wc,gc,?_⟩
  intro Y M I inst c w y m e fees tail home tp paid
  have approach:Tendsto (fun k=>Y k-∑b,c b*M b k) (ℓ:Filter (ℕ×ℕ))
      (𝓝 (appeared F near X r.val ψ-∑b,c b*X.charge F h (out b))):=
    full.sub (tendsto_finsetSum _ fun b _=>(gram b).const_mul (c b))
  apply le_of_tendsto_of_frequently approach.norm
  apply paid.mono
  rintro k ⟨measured,columns,funded,far⟩
  apply (finite c (w k) (Y k) (fun b=>M b k) (y k) (m k) e fees measured columns).trans
  apply add_le_add le_rfl
  calc (∑i,‖w k i‖*‖y k i-∑b,c b*m k i b‖)≤∑i,‖w k i‖*tail:=sum_le_sum fun i _=>
         mul_le_mul_of_nonneg_left (far i) (norm_nonneg _)
       _=(∑i,‖w k i‖)*tail:=(Finset.sum_mul _ _ _).symm
       _≤_:=mul_le_mul_of_nonneg_right funded tp

end YM.Integration.WilsonMovingForkConvolvedResidual
end
