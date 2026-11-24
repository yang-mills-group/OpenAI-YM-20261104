import YM.OPE.Compatible.Glim.Rib
/-! # script operation multiplication. Payers. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d m:ℕ}{I J:Type*}
noncomputable def Bake(p:Script I i)(q:Script I j):Script I (i+j):= Sack.rope (fun k:Page I i × Page I j=>Fin.append k.1 k.2) (fun k=>p k.1*q k.2)
lemma BakePair (p:Script I i)(q:Script I j)(x y:ℝ)(h:soot m p x)(hh:soot m q y): soot m (Bake p q) (x*y):=by
     let u(k:Page I i × Page I j):= Page.figure m k.1*Page.figure m k.2; let f(k:Page I i × Page I j):= p k.1*q k.2; have he:Sack u f (x*y):=Sack.multiplex h hh (fun i=>by unfold u f; rw [norm_mul]; exact le_of_eq (by ring)) (fun i=> mul_nonneg (zero_le_one.trans (payer m _)) (zero_le_one.trans (payer m _)))
     rw [← mul_one (x*y)]; refine Sack.cart _ he zero_le_one (payer _) ?_; intro z; unfold u Page.figure poise; rw [← mul_pow,mul_one]; apply pow_le_pow_left₀ (by positivity); exact_mod_cast (show stamp (Fin.append z.1 z.2) ≤ _*_ from (by have ht :1 ≤ stamp z.1:= notch_one ..; have hh:1 ≤ stamp z.2:=notch_one ..; have hv:=span_join z.1 z.2; nlinarith only [ht,hh,hv])) -- positivity over nat
variable [Fintype I] {n:Side}
lemma BakeReading (p:Script I i)(q:Script I j)(x y:ℝ)(h:soot m p x)(hh:soot m q y)(z:Site n)(v:deck I n):Flume.Script.value z (Bake p q) v= Flume.Script.value z p v*Flume.Script.value z q v:=by
     let a:= fun _:Fin (i+j)=>v; let b:= fun _:Fin i=>v; let c:=fun _:Fin j=>v; let f(i:Page I i):=p i* render z i b; let g(j:Page I j):= q j* render z j c; let P(k:Page I i × Page I j):= p k.1*q k.2; let Q(k:Page I i × Page I j):=Fin.append k.1 k.2; have he(k k'):render z (Q (k,k')) a= render z k b*render z k' c:=by unfold Q render a b c; rw [Fin.prod_univ_add];simp only [Fin.append_left,Fin.append_right]
     have ht:Summable f:=(instruments _ (sootS h) z _).summable; have hq:Summable g:=(instruments _ (sootS hh) z _).summable; have hx:Summable fun v:Page I i × Page I j=> f v.1 * g v.2:=(ht.norm.mul_norm hq.norm).of_norm; have hz(k:Page I i × Page I j): f k.1 *g k.2=P k* render z (Q k) a:=by rw [show Q k=_ from (show Q k=Q (k.1,k.2) from rfl),he]; unfold f g P;ring
     unfold Bake Flume.Script.value scribe; change (∑' i, Sack.rope Q P i*render z i a)= (∑' i,f i)*(∑' i,g i); rw [ht.tsum_mul_tsum hq hx, tsum_congr hz,Sack.cart_bill Q _ ?_]; show Summable _; simpa only [hz] using hx
end YM.OPE.Flume.Script
