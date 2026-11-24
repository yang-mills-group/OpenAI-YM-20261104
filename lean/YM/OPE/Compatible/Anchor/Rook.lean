import YM.OPE.Compatible.Anchor.Wheel
/-! # Motor generators -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08 Maxwell
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
-- primitive.P diverger.Repag
noncomputable def twist (h:i=j) : Taylor G i→ₗ[ℝ] Taylor G j:=by subst j; exact LinearMap.id
lemma twistSal (h:i=j)(x:Taylor G i): twist h x=h ▸ x:=by subst i;rfl
lemma ribbon_m (h:i=j)(x:Taylor G i)(v:G.El): twist h (Taylor.paint v x)= Taylor.paint v (twist h x):=by subst i;rfl
noncomputable abbrev pat (g:Fin d) : Taylor G g.val →ₗ[ℝ] Alphabet G d:= LinearMap.single ℝ (fun j:Fin d=>Taylor G j.val) g
noncomputable abbrev Rosary (g:Fin d)(h:g.val=k+1): BoxC G k→ₗ[ℝ] Alphabet G d:= pat g ∘ₗ twist h.symm ∘ₗ wheelC G k
lemma Raylet (h:i=j)(u:Taylor G i): twist h.symm (armK G j (twist h u))=armK G i u:=by subst j;rfl
lemma RosaryTurn (g:Fin d)(h:g.val=k+1)(x: BoxC G k)(s:G.El): Rosary g h (Ahorn s x)=spray s (Rosary g h x):=by
    let f:= wheelC G k; rw [show Rosary g h (Ahorn s x)= monoX g (twist h.symm (Taylor.paint s (f x))) from congr_arg (fun u=> monoX g (twist h.symm u)) (DFunLike.congr_fun ((μIncome (k:=k) (G:=G)).choose_spec.1 s) x), ribbon_m]; exact (spray_one ..).symm
-- Basis to multilinear.P. use ∃ Turner with property thrust
lemma homeAd (u:G.Color)(g:G.El): G.adjoint g (G.adjoint g⁻¹ u)=u:=by rw [←G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
lemma wireEF (E:I→Type)[Fintype I][∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,FiniteDimensional ℝ (E i)][NormedAddCommGroup F][NormedSpace ℝ F] (A: MultilinearMap ℝ E F):∃ B: ContinuousMultilinearMap ℝ E F,B.toMultilinearMap=A:=by
    let t(i):= Fin (finrank ℝ (E i)); let e(i):=Module.finBasis ℝ (E i); let p:= ∑ i: (j:I)→ t j, ((ContinuousMultilinearMap.mkPiAlgebra ℝ I ℝ).compContinuousLinearMap fun j=>((e j).coord (i j)).toContinuousLinearMap).smulRight (A (fun j=>(e j) (i j)))
    refine ⟨p,MultilinearMap.ext (fun x =>?_ )⟩; let f(i:I)(a:t i):= (e i).repr (x i) a • e i a; change p x=A x; rw [show A x=A (fun i=>∑ a:t i,f i a) from congr_arg A (funext fun i=> ((e i).sum_repr (x i)).symm),A.map_sum_finset]; unfold p; rw [_root_.sum_apply]; simp only [Fintype.piFinset_univ]; exact sum_congr rfl fun i _=> (A.map_smul_univ (fun j=>(e j).repr (x j) (i j)) (fun j=> (e j) (i j))).symm
lemma polyVe {a:Fin r→Fin k}(T:G.Color→ₗ[ℝ] MultilinearMap ℝ (fun i=> Taylor G (a i).val) ℝ)(h:∀ u p z,T (G.adjoint u p) (fun j=> Taylor.paint u (z j))= T p z):
    ∃ f: SpiceK G a,Abalo f ∧∀ x p,T p x=Dotty p (f x):=by
      let f(i:G.ColorIndex):= T (Phone G i); let Y:MultilinearMap ℝ _ G.Color:={
           toFun x:= WithLp.toLp 2 (fun i=> f i x)
           map_update_add' x i v w:=by ext1 j; exact (f j).map_update_add ..
           map_update_smul' x i c v:=by ext1 j; exact (f j).map_update_smul .. }
      obtain ⟨V,hv⟩:=wireEF (F:=G.Color) (I:= Fin r) (fun i=> Taylor G (a i).val) Y; have ht(x p): T p x = Dotty p (V x):=by
           change T p x= Dotty p (V.toMultilinearMap x); rw [hv]; nth_rw 1 [← (Awake (G:=G)).sum_repr p]; rw [map_sum,_root_.sum_apply]; apply sum_congr rfl; intro i _;rw [map_smul,_root_.smul_apply]; change p i *(T ((Awake (G:=G)) i) x)=p i * (Y x i); rfl -- basis
      refine ⟨V,fun u p=>sepDot fun x=>?_,ht⟩; rw [←ht, ← homeAd x u, hubAD,h,ht]
end YM.OPE.Variance
