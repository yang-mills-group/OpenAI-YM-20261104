import YM.MS.Rock.Houses
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Health
/-!
# Integer real measure For compact supports

Integrability direct; later continuation extends to any rib. Use for Cycle algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Landau Arts Pilot Spin Arc Wire Path
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup P][NormedSpace ℝ P][MeasurableSpace P][BorelSpace P][FiniteDimensional ℝ P]{b c: Bool}{m:ℕ}{A B:ℝ}{U V:Rip G}{F H:Mob G}
lemma turf_cost (h:kPrice F)(n:ℕ) {w:tagSmooth E (Cfield G n) (SectorP n)}(hv: Trail w): ContDiff ℝ ∞ (fun i=>F n (walk0 w i)):= by
   -- canonical chart finite from Local tile or recursion P: cost work. Need arbitrary non-linear shifts (t:any). choose construction list induction ∃ lifted CLM K(P) finite. 
   suffices ht: ∃ (D:Type) (_i: NormedAddCommGroup D) (_j: NormedSpace ℝ D) (_k:FiniteDimensional ℝ D)(f:E→D)(K:Touch G n D), ContDiff ℝ ∞ f ∧∀ i, walk0 w i=sail K (f i) by -- existential dependencies class `@` not instances? use nonempty
       obtain ⟨D,i,j,k,f,K,hf,H⟩:= ht; simp_rw [H]; exact ((h n D K).smooth ()).comp hf
   induction w with
   | nil=> exact ⟨E,inferInstance,inferInstance,inferInstance,id,[],contDiff_id,fun _=>rfl⟩
   | cons a l ih=>
       obtain ⟨D,i,j,k,f,K,hf,H⟩:= ih hv.rest; let p:=ContinuousLinearMap.fst ℝ (SectorP n) D; let q:=ContinuousLinearMap.snd ℝ (SectorP n) D; refine ⟨SectorP n × D, inferInstance,inferInstance,inferInstance,fun i=>(a.2 i,f i),(a.1,p):: Wire.lift K q,(hv a (by simp)).prodMk hf,fun x=>?_⟩; change (a.1,a.2 x)::walk0 l x=_; rw [sail_cons,lift_sail,H]; rfl
-- fixed list variant with prefix cons handy.
def constX (E:Type)(l:Legs (Shore G m)): tagSmooth E (Cfield G m) (SectorP m) := l.map fun i=> (i.1,fun _=> i.2)
omit [FiniteDimensional ℝ E] in
lemma plain0 (l:Legs (Shore G m)): Trail (constX E l):= by intro i hi; obtain ⟨i,hi,rfl⟩:= List.mem_map.mp hi; exact contDiff_const
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma plainX (l:Legs (Shore G m))(x:E): walk0 (constX E l) x=l:= by simp only [constX,walk0,List.map_map]; convert! List.map_id l; -- eta
lemma far_support (F:P→ℂ)(h:Continuous F)(hh:∀ i, A<‖i‖→ F i=0)(μ:Measure P)[IsFiniteMeasureOnCompacts μ]: Integrable F μ:= by
    have hf : HasCompactSupport F:= by refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:P) A) ?_; intro i hi; exact mem_closedBall_zero_iff.mpr (le_of_not_gt (fun he=>hi (hh i he)))
    exact h.integrable_of_hasCompactSupport hf
variable (hf:kPrice F)(hH:kPrice H)(hu:rPrice U)(hv:rPrice V)
abbrev Tq {n:ℕ}(U V:Ridge G n)(p q:SectorP n)(f:Rack G n):= trc U p (trc V q f)
include hf hu hv
lemma tt_double (n:ℕ)(l:Legs (Shore G n))(hA:rock A U)(hB:rock B V): Integrable (fun q: SectorP n × SectorP n=> Tq (U n) (V n) q.1 q.2 (F n) l) ((Px n).prod (Px n)):= by
    let E:=SectorP n; let T:= constX (E× E) l; have ht : Trail T:= plain0 _
    have hF: Continuous (fun q:E× E=>Tq (U n) (V n) q.1 q.2 (F n) l):= by
       simp_rw [Tq,at_trc]; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _; refine (((hu n i j 0).smooth ()).continuous.comp continuous_fst).mul (continuous_finsetSum _ (fun a _=>?_)) -- finite? inspect LE
       refine continuous_finsetSum _ (fun b _=> ((((hv n a b 0).smooth ()).continuous.comp continuous_snd).mul ?_))
       convert! (turf_cost (E:=E×E) hf n (w:=(a,Prod.snd)::(b,-Prod.snd)::(i,Prod.fst)::(j,-Prod.fst)::T) (((((ht.cons j _ contDiff_fst.neg).cons i _ contDiff_fst).cons b _ contDiff_snd.neg).cons a _ contDiff_snd))).continuous using 1; ext x; change F n (_ :: _ :: _ :: _ :: l)= F n (_ :: _ :: _ :: _ :: walk0 T x); rw [plainX]; rfl -- wrong loop
    unfold Px; refine far_support _ hF (A:=max A B) ?_ _; intro i hi; rw [Prod.norm_def,lt_max_iff] at hi;
    rcases hi with he|he; · simp only [Tq,at_trc]; simp_rw [hA n _ _ _ (lt_of_le_of_lt (le_max_left ..) he),zero_mul,Finset.sum_const_zero]
    simp only [Tq,at_trc]; simp_rw [hB n _ _ _ (lt_of_le_of_lt (le_max_right ..) he), zero_mul,Finset.sum_const_zero, mul_zero, Finset.sum_const_zero]
end YM.MS.Rock
