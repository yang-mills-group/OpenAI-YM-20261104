import YM.X.Site.Ocean
import YM.Extraction.Round
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
# Cover Riemann summation voxel. physical Euclidean positions not configs. no lift; uses ceil. finite support per sampling.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print
open scoped Topology BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {G:Gauge} {t:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable (x:E4)(z:Cover) (ht:0<t)
def index (t:ℝ)(x:E4):Cover:= fun a=> ⌈x a/t⌉
def voxel (t:ℝ)(z:Cover): Set E4:= {x| index t x=z}
lemma voxel₁ (y:Cover)(h:x∈voxel t y): index t x=y:=h
include ht
lemma static : voxel t z= WithLp.ofLp ⁻¹' Set.pi univ (fun w:Axis=> Extraction.tile t (z w)):= by
   ext1 x; constructor
   · intro h w _; exact (Extraction.tile_bounds ht _ _).mp (congr_fun (voxel₁ x z h) w)
   intro h; refine (show index t x=z from ?_); exact funext fun w=> (Extraction.tile_bounds ht _ _).mpr (h w (mem_univ w)) -- mem apply
lemma voxel_meas : MeasurableSet (voxel t z):= by rw [static z ht]; exact (PiLp.volume_preserving_ofLp _).measurable (MeasurableSet.pi countable_univ (fun _ _=>measurableSet_Ioc))
lemma voxel_vol : volume (voxel t z)= ENNReal.ofReal (t^4):= by
   rw [static z ht,(PiLp.volume_preserving_ofLp _).measure_preimage]; · change (Measure.pi (fun _:Axis=>volume)) (Set.pi _ _) = _; rw [Measure.pi_pi]; simp_rw [Extraction.tile,Real.volume_Ioc]; have he(i:Axis): ENNReal.ofReal (t*(z i)-t*((z i)-1))= ENNReal.ofReal t:= congr_arg _ (by ring); simp_rw [he]; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin, ← ENNReal.ofReal_pow ht.le]
   exact (MeasurableSet.pi countable_univ (fun i _=> measurableSet_Ioc)).nullMeasurableSet
lemma voxel_near : dist (spot t (index t x)) x ≤ 4*t:= by
   rw [dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (by positivity), EuclideanSpace.real_norm_sq_eq]; refine le_trans (b:=∑ _ : Axis,t^2) (Finset.sum_le_sum ?_) ?_; intro i _
   · refine sq_le_sq.mpr ?_; rw [abs_of_pos ht]; exact Extraction.coord_grid_bound (n:=1) ht (points (fun _=>x)) 0 i
   simp; nlinarith [sq_nonneg t]
omit ht
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
def mosaic (t:ℝ)(f:Cover→V)(x:E4) := f (index t x)
include hq in
lemma entrant : plot q (fun i=> index (ε i) x) x:= by
   unfold plot; rw [tendsto_iff_dist_tendsto_zero]; refine squeeze_zero (fun i=>dist_nonneg) (fun i=>voxel_near x (epsilon_pos q i)) ?_; simpa only [mul_zero] using! (paths hq).cutoff.const_mul 4
variable {f:Cover→V}{w:Finset Cover}
def Frugal (f:Cover→V)(w:Finset Cover): Prop:= Function.support f⊆ w
lemma mosaic_eq (h:Frugal f w): mosaic t f x=∑ z∈w, (voxel t z).indicator (fun _:E4=> f z) x:= by
   unfold mosaic; rw [Finset.sum_eq_single (index t x)]; rw [Set.indicator_of_mem (show x∈voxel t (index t x) from rfl)]; intro b _ he; rw [indicator_of_notMem (fun p=> he (voxel₁ x b p).symm)]
   intro h'; rw [show f (index t x)=0 from notMem_support.mp (fun y=> h' (h y)), Set.indicator_of_mem (show x∈voxel t (index t x) from rfl)]
lemma prism(ht:0<t): Integrable ((voxel t z).indicator (fun _:E4=> f z)):= (integrable_indicator_iff (voxel_meas z ht)).2 (integrableOn_const (by rw [voxel_vol z ht]; exact ENNReal.ofReal_ne_top))
lemma mosaic_ok (ht:0<t)(h:Frugal f w):Integrable (mosaic t f):= by
   rw [show mosaic t f=(fun x=>∑ z∈w, (voxel t z).indicator (fun _:E4=> f z) x) from funext fun x=>mosaic_eq (t:=t) x h]; apply integrable_finsetSum; intro i _; exact prism i ht
lemma mosaic_sum [CompleteSpace V](ht:0<t)(h:Frugal f w): ∫ x:E4, mosaic t f x= t^4 • ∑ z∈w,f z:= by
   simp_rw [mosaic_eq _ h]; rw [integral_finsetSum, Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [integral_indicator (voxel_meas _ ht),setIntegral_const,Measure.real,voxel_vol _ ht,ENNReal.toReal_ofReal (by positivity)]
   intro i _; exact prism i ht

end YM.PositionX.Haze
