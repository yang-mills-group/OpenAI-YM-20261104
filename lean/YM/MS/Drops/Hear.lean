import YM.MS.Drops.Phase
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
/-! Radian to MS chart.
Dimension fixed=4. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Drops
open Set Function Filter Finset Metric MeasureTheory Real
open Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Analysis Labels Maxwell Theater Next Next.Rank Next.Rank.Beamer Tone High Rake Osc Snap
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
open City Latch
variable {G:Gauge}{h n:ℤ}{f g:Local.BV.Grade G}{s:ℝ}{p:FourP} {k i:Axis}
def xy (f g: Local.BV.Grade G)(p:FourP) : ℂ:= ∑ i:G.ColorIndex,∑ k:Axis, f (W k i p)*g (W k i (-p))
abbrev Cdeg (f g: Local.BV.Grade G)(s:ℝ)(p:FourP):= ∑ i:BH G,∑ j:BH G,(PlanetD G s i j p)* f (i,p)*g (j,-p)
abbrev Rad (s:ℝ)(p:FourP):ℝ:= exp s * City.brush (exp s) p
lemma tallyS (X:BH G→ℂ)(hp:∀ i:BH G, i.1.1.isNone ∨ i.1.2→ X i=0):∑ i:BH G,X i=∑ i: Axis,∑ j:G.ColorIndex, X (Landau.gauge i,j):= by
    unfold BH Branch Leg Landau.Atom; simp [ Fintype.sum_prod_type, Fintype.sum_option, show ∀ i:BH G, i.1.1.isNone ∨ i.1.2= true→ X i=0 from hp, Landau.gauge ] -- hypothesis coerc @Cfield.
lemma transverse (hp:Horizontal f h)(hr:Horizontal g n)(p:FourP)(k:Axis)(c:G.ColorIndex) : ∑ i:BH G,(PlanetD G s i (Landau.gauge k,c) p)* f (i,p)=(Rad s p :ℂ )*((Momentum.sq p:ℂ)*f (W k c p)):= by
    have he(x:BH G)(hx:x.1.1.isNone ∨ x.1.2=true): f (x,p)=0:= by by_contra h; obtain ⟨u,v,q,H⟩:= Tall_l hp (x,p) h; rw [show x=( Landau.gauge u,v ) from congr_arg Prod.fst H] at hx; simp [Landau.gauge] at hx
    rw [tallyS _ fun i h=> mul_eq_zero_of_right _ (he i h) ]; let r:=exp s; have ht (i:Axis)(u:G.ColorIndex): PlanetD G s (Landau.gauge i,u) (Landau.gauge k,c) p= if u=c then (Rad s p:ℂ)*( precision i k p:ℂ) else 0:= by unfold PlanetD High.spaceD Landau.zD Landau.choir; refine if_ctx_congr Iff.rfl (fun h=>?_) (fun _=>rfl); rw [ ← City.brushed ]; unfold L0 Rad; simp only [ Landau.gauge, Complex.ofReal_mul,id_eq ]; ring -- simpl mismatch
    simp_rw [ht]; rw [show (∑ i:Axis,∑ x:G.ColorIndex,(if x=c then (Rad s p:ℂ)*( precision i k p:ℂ) else 0)*_)=∑ i:Axis,(Rad s p:ℂ)*((precision i k p:ℂ)* f (W i c p)) from ?_]; swap; · simp [ite_mul,mul_assoc,W] -- W def obscure
    rw [ ← Finset.mul_sum ]; apply congr_arg; have he : (∑ i:Axis,(↑(delta i k (Momentum.sq p)):ℂ)*f ( W i c p ))=(Momentum.sq p:ℂ)*f (W k c p):= by simp [Landau.delta,apply_ite,ite_mul]
    unfold precision; simp only [Complex.ofReal_sub, Complex.ofReal_mul,sub_mul, Finset.sum_sub_distrib,he]; simp_rw [mul_comm (_:ℂ) (p k:ℂ), mul_assoc (p k:ℂ), ← Finset.mul_sum, across hp,mul_zero,sub_zero] -- too broad
include s
lemma vertical (hp:Horizontal f h)(hr:Horizontal g n)(p:FourP): Cdeg f g s p=(Rad s p:ℂ)*( Momentum.sq p:ℂ )*xy f g p:= by
    have he(x:BH G)(hx:x.1.1.isNone ∨ x.1.2=true): g (x,-p)=0:= by by_contra h; obtain ⟨u,v,q,H⟩:= Tall_l hr (x,-p) h; rw [show x=( Landau.gauge u,v ) from congr_arg Prod.fst H] at hx; simp [Landau.gauge] at hx
    unfold Cdeg; rw [ Finset.sum_comm ]; simp_rw [← Finset.sum_mul ]; rw [tallyS _ (fun i h=> mul_eq_zero_of_right _ (he i h)), Finset.sum_comm]; unfold xy; simp_rw [Finset.mul_sum,transverse hp hr ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun k _=> ?_; rw [ ← mul_assoc, mul_assoc ]; -- loop simp; infer
end YM.MS.Drops
