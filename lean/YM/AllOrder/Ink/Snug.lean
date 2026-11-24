import YM.AllOrder.Ink.Twirl
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open Field GaussianScore
variable (F:Stalk α α)(U V:Field α) (X:rule α n) (z:Site n)
local notation "L"=> Slip (Point α)
variable (ha:0≤a)(hv:Belt F a D)
include ha hv
lemma lit (u v : L) : (∑ p:LeafIdx u,∑ q:LeafIdx v,∑' w:Cover, spur F u v p q w *invoice z (jointI u v p q w) X)=∑ y:Site n,spark F (invoice z u) (invoice y v) X:= by
   simp_rw [(latency F z _ _ _ _ X hv ha).tsum_eq, coin F, Finset.sum_apply, Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; symm; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun p _=> Finset.sum_comm)
variable {D':ℝ}(hD:0≤D)(he:U.Good a C k)(hq:V.Good a D' N)(hh:0≤b)(hy:b*(N+1:ℕ) ≤ a)
include hh hy hD he hq
lemma rates : (embrace F U V).site n z X= spark F (U.site n z) (V.table n) X:= by
  let G:= embrace F U V; let f : Family U V→ℝ:=fun i=> G.fee i *invoice z (G.slip i) X; have hg:= gain_spark F U V hh hy he hq hv hD; let B(i:U.Ty):= invoice z (U.slip i)
  have hf:Summable f:= hg.total hh z X; change ∑' i:Family U V,f i=_; rw [hf.tsum_sigma, ← (he.tests ha z (F:=fun u=> spark F u (V.table n) X) (toolA F k _ X).2).tsum_eq]; apply tsum_congr; intro i
  rw [(hf.sigma_factor i).tsum_sigma]; change _ = U.fee i* spark F (B i) (V.table n) X
  let W(j:V.Ty)(y:Site n):= invoice y (V.slip j); let T (v: rule α n→ℝ):= spark F (B i) v X
  have hu : T (V.table n) = ∑' j:V.Ty, V.fee j*∑ y:Site n,T (W j y):= by
     have hx : LinTest _ N T:=(toolA ..).1; rw [table,hx.finiteTest _ _ (fun y _=>(hq.site ha y).2.1)]; have hs(y:Site n): HasSum (fun j=> V.fee j*T (W j y)) (T (V.site n y)):= hq.tests ha y hx; simp_rw [← show ∀ y : Site n,(∑' j, V.fee j*T (W j y))= T (V.site n y) from fun y=>(hs y).tsum_eq]; rw [← Summable.tsum_finsetSum (fun i (_:i∈(Finset.univ:Finset (Site n)))=>(hs i).summable)]
     exact tsum_congr fun j=> (Finset.mul_sum ..).symm
  rw [show spark F (B i) (V.table n) X=_ from hu, ← tsum_mul_left]; apply tsum_congr; intro j
  let H:= (hf.sigma_factor i).sigma_factor j; rw [H.tsum_sigma, tsum_fintype]; simp_rw [(H.sigma_factor _).tsum_sigma]; change ∑ p, (∑' _ : LeafIdx (V.slip j),_)=_ -- underscores
  rw [← lit F X z ha hv (U.slip i) (V.slip j)]; simp_rw [tsum_fintype (β:= LeafIdx (V.slip j)), Finset.mul_sum, ← tsum_mul_left]; -- Param name type
  apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _; exact tsum_congr fun w=> show U.fee i*(V.fee j* _)*_= _ from (by ring_nf; rfl)
-- total equality
lemma embracing (n:Side): spark F (U.table n) (V.table n)= (embrace F U V).table n:= by
   ext1 x; rw [table_apply, show spark F (U.table n) (V.table n) x= ∑ i: Site n,spark F (U.site n i) (V.table n) x from ((toolA F k _ x).2).finiteTest _ _ (fun i _=> (he.site ha i).2.1)]; apply Finset.sum_congr rfl; intro i _; exact (rates F U V x i ha hv hD he hq hh hy).symm
end Method
end YM.AllOrder.Ink
