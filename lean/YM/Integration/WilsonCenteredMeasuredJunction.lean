import YM.Integration.WilsonCenteredBornHearing

/-! The measured input coordinates can converge on the original reporting layout,
whose filter refines the ordered Wilson limit. Keep their cutoff dependence inside
each real Wilson integral. Each fixed basis entry has the original ordered limit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredMeasuredJunction
open Function Set Filter Analysis Table Work.A01 Work.A05 MeasureTheory StressFlux.Matching
open Extraction Lattice Cells Wilson Metric FrontierTrace.Primary.Junction
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval Classical
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book} {n:ℕ}
variable {X:Type*}[TopologicalSpace X][MeasurableSpace X][BorelSpace X] {μ:Measure X}
private abbrev Seats (C:Family G)(d:Caps n):= (i:Fin n)→(C.book.coord (d i)).Index
private def field {d:Caps n} (j:Seats C d):C.book.Vector d:=fun i=>dial (L:=C.book) d i (j i)
private def coeff {d:Caps n}(v:C.book.Vector d)(j:Seats C d):ℂ:=∏i,(dial (L:=C.book) d i).repr (v i) (j i)
private theorem expand {d:Caps n}(M:Moment C.book n d)(v:C.book.Vector d):
    M v=∑j:Seats C d, coeff v j*M (field j):=by
  let b:=dial (L:=C.book) d
  have e:v=fun i=>∑k,(b i).repr (v i) k • b i k:=funext fun i=>((b i).sum_repr _).symm
  conv_lhs=>rw [e]
  rw [MultilinearMap.map_sum]
  exact Finset.sum_congr rfl (fun j _=>M.map_smul_univ (fun i=>(b i).repr (v i) (j i)) _)
omit [TopologicalSpace X] [BorelSpace X] in
private theorem integrated {d:Caps n}(T:Table C.book)(L:X→Points n)(φ:X→ℂ)(v:C.book.Vector d)
    (priced:∀j:Seats C d,Integrable (fun x=>φ x*T.value d (L x) (field j)) μ):
    (∫x,φ x*T.value d (L x) v ∂μ)=∑j:Seats C d,coeff v j*(∫x,φ x*T.value d (L x) (field j) ∂μ):=by
  conv_lhs=>enter [2,x,2];rw [expand (T.value ..) v]
  simp_rw [Finset.mul_sum,← integral_const_mul (coeff v _),mul_left_comm (φ _) (coeff v _)]
  exact integral_finsetSum _ (fun j _=>(priced j).const_mul (coeff v j))

theorem original (F:Spec.Final C f S){l:Filter (ℕ×ℕ)} (law:l≤f.fuse)
    {d:Caps n}{K:Set X}(L:X→Points n)(φ:X→ℂ)(v:C.book.Vector d)(w:ℕ×ℕ→C.book.Vector d)
    (control:Wcmain C)(map:Continuous L)(compact:IsCompact K)(clear:∀x∈K,L x∈conf n)
    (inK:∀ᵐ x ∂μ,x∈K)(inGood:∀ᵐ x ∂μ,L x∈generic n)(test:Integrable φ μ)
    (moves:∀i,Tendsto (fun y=>w y i) l (𝓝 (v i))) :
    Tendsto (fun i:ℕ×ℕ=>∫x,φ x*(rounded C i.1 i.2).value d (L x) (w i) ∂μ) l
      (𝓝 (∫x,φ x*S.value d (L x) v ∂μ)) :=by
  have basis (j:Seats C d) := (Extraction.Order.along (junction_tail F
    (fun i=>⟨d i,field j i⟩) L φ control map compact clear inK inGood test).choose_spec).mono_left law
  have c (j:Seats C d):Tendsto (fun y=>coeff (w y) j) l (𝓝 (coeff v j)) :=
    tendsto_finsetProd _ (fun i _=>((dial (L:=C.book) d i).coord (j i)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (moves i))
  rw [integrated S L φ v (fun j=>junction_int F L map φ test compact clear inK (field j))]
  apply (tendsto_finsetSum Finset.univ (fun (j:Seats C d) _=>(c j).mul (basis j))).congr'
  exact Eventually.of_forall fun k=>(integrated (rounded C k.1 k.2) L φ (w k)
    (fun j=>ready_to_use (fun i=>⟨d i,field j i⟩) L φ map.measurable test k.1 k.2)).symm

end YM.Integration.WilsonCenteredMeasuredJunction
