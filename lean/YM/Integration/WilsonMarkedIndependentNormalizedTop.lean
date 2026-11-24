import YM.Integration.WilsonPhysicalMarkedDefectFinePrimaryPlume
import YM.Integration.WilsonMarkedIndependentNormalizedElection

/-! Exact folding of the complete top field, including the original label,
all powers of its filed coordinate and every actual microscopic translate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedTop
open Function Finset Lattice Wilson RG Source Labels Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos.Polestar Work.F08 Stationary
open PowerSeries
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem scale {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
    {r:ℕ}{A:ℝ}(F:Ten V (YForest G) r)(h:Cork terrain 0 1 A F)(c:ℝ)(n:Side):
    plume (c • F) n=c • plume F n:=by
  exact plume_map F h zero_lt_one (c • ContinuousLinearMap.id ℝ V) n

/-- A Laurent or formal coordinate on the entire local field stencil also has
zero bare finite-period error, at every field and coupling rank. -/
theorem field {h D:ℕ}{F:Frame G h}(T:SectionData F)(w:h<D)(X:Verse F)
    (A:Levels G)(O:ChartRatio G)(N:ℕ)(n:Side)(e r:ℕ):
    let Y:=Shrine (Peaks A O T w N N) X
    ∃B,Cork terrain 0 1 B (Y.2 e r) ∧ plume (Y.2 e r) n=Y.1 n e r:=by
  intro Y
  let V:=fun (a:Alma F)(j:ℕ×ℕ)=>coeff j.1 (X a) • anthem T w a j.2 r
  let Vn:=fun (a:Alma F)(j:ℕ×ℕ)=>coeff j.1 (X a) • herald T w a n j.2 r
  let b(a:Alma F)(j:ℕ×ℕ):=‖coeff j.1 (X a)‖*(covered T w a j.2 r 1).choose
  have paid(a:Alma F)(j:ℕ×ℕ):Cork terrain 0 1 (b a j) (V a j):=
    (Cork.μ (show Cork terrain 0 1 _ (anthem T w a j.2 r) from (covered T w a j.2 r 1).choose_spec) _)
  have each(a:Alma F)(j:ℕ×ℕ):plume (V a j) n=Vn a j:=by
    apply (scale _ (show Cork terrain 0 1 _ _ from (covered T w a j.2 r 1).choose_spec) _ n).trans
    exact congrArg (coeff j.1 (X a) • ·) (WilsonPhysicalMarkedDefect.FinePrimary.local_fold T w a n j.2 r)
  have orig:Y.2 e r=∑a,∑j∈antidiagonal e,V a j:=by
    simp only [Y,Peak_initial,Shrine,Prod.snd_sum,Finset.sum_apply,Stem,affix,vein,Pi.smul_apply,V]
  have copy:Y.1 n e r=∑a,∑j∈antidiagonal e,Vn a j:=by
    simp only [Y,Peak_initial,Shrine,Prod.fst_sum,Finset.sum_apply,Stem,affix,vein,Pi.smul_apply,Vn]
  have inside(a:Alma F):Cork terrain 0 1 (∑j∈antidiagonal e,b a j) (∑j∈antidiagonal e,V a j):=
    Cork.sum (fun j _=>paid a j)
  rw [orig,copy]
  refine ⟨_,Cork.sum (fun a _=>inside a),?_⟩
  rw [plume_spurs univ (fun a _=>inside a) zero_lt_one n]
  apply sum_congr rfl
  intro a _
  rw [plume_spurs (antidiagonal e) (fun j _=>paid a j) zero_lt_one n]
  exact sum_congr rfl (fun j _=>each a j)

theorem original {ι:Type}[DecidableEq ι](Q:ι→SealR G)(A:Levels G)(O:ChartRatio G)(N m:ℕ)
    (X:∀s,Verse (Q s).F)(p:ι → Cover)(S:Finset ι)(n:Side)(e r:ℕ):
    let Y:=coatA A O N m Q X p S
    plume (Y.2 e r) n=Y.1 n e r:=by
  intro Y
  by_cases single:S.card=1
  · obtain ⟨s,rfl⟩:=Finset.card_eq_one.mp single
    change plume ((coatA A O N m Q X p {s}).2 e r) n=(coatA A O N m Q X p {s}).1 n e r
    rw [coatLeaf]
    let H:=centralL A O N m N (Q s) (X s)
    obtain ⟨B,price,same⟩:=field (Q s).ans (Q s).path
      (steep A O (Q s).ans (Q s).path N m (N-m) (X s)) A O N n e r
    change plume (H.2 e r) n=H.1 n e r at same
    change Cork terrain 0 1 B (H.2 e r) at price
    change plume (revolve (p s) ((petal (fun i=>(Q i).D) s) ∘ H.2 e r)) n =
      revolve (wrap n (p s)) ((petal (fun i=>(Q i).D) s) ∘ H.1 n e r)
    rw [sigmaMint,plume_map _ price zero_lt_one (petal (fun i=>(Q i).D) s) n,same]
  · have zero:Y=0:=coatLazy A O N m Q X p S single
    rw [zero]
    exact plume_zero ..

end YM.Integration.WilsonMarkedIndependentNormalizedTop
end
