import YM.OPE.Compatible.Speke.Wood
/-!
# Low multiplicity awards
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
open Pose (epic)
variable {U:Gloam}{d r:ℝ}{K:ℕ→ℕ}{k j l m:ℕ}{X Y Z: Panels} {A:Zem}{p q t:Pose}
structure Woody (U:Gloam)(K:ℕ→ℕ) (d:ℝ):Prop where
   station:Crown U K
   funding : ∃ r<d,∀ᶠ i in atTop,U.h i* K i ≤ r
lemma never (hs:Woody U K d)(hm:m+4=k+1+j+l)(hp:∀ i, Port U d k (X i))(hq:∀ i,Port U d j (Y i))(hr:∀ i, Port U d l (Z i)): Fruit U m (Triad K A X Y Z) 0:=by
    obtain ⟨t,ht,H⟩:= hs.funding; apply receiptV; intro x y; apply hotNone; intro v
    let g:=dart X x y *plume Y x y v.1 *plume Z x y v.2; have hh:= (plant x y hp|>.mool (parcelC x y v.1 hq)).mool (parcelC x y v.2 hr)
    rw [show TimeA K X Y Z x y v=Oct K (fun _=>1) g from funext fun i=>by unfold TimeA Oct g;simp only [one_mul,Pi.mul_apply]]; exact brain hs.station (by omega) (by omega :3+0=3) hh ht H zero_le_one (fun x=>by simp) -- hf signature ∀x
lemma onceC (hs:Woody U K d)(hm:m+4=p.heat+1+1+k+j)(hp:∀ i,Port U d k (Y i))(hq:∀ i,Port U d j (Z i)): Fruit U m (Triad K A (SinB p) Y Z) 0:=by
   obtain ⟨t,ht,H⟩:=hs.funding; apply receiptV; intro x y; apply hotNone; intro v; let g:=plume Y x y v.1*plume Z x y v.2
   have he:= lettr_step p x y; have hh:= nu_shape p
   rw [show TimeA K (SinB p) Y Z x y v=Oct K _ g from (show TimeA K (SinB p) Y Z x y v=Oct K (dart (SinB p) x y 0) g from funext fun i=>Finset.sum_congr rfl fun u _=>by change dart (SinB p) x y 0 u*_ *_= dart (SinB p) x y 0 u*(_*_);ring)]
   exact alone he ((parcelC _ _ _ hp).mool (parcelC _ _ _ hq)) hs.station ht H (by omega)
lemma onceS (hs:Woody U K d)(hm:m+4=k+1+j+(p.heat+1))(hp:∀ i,Port U d k (X i))(hq:∀ i,Port U d j (Y i)): Fruit U m (Triad K A X Y (SinB p)) 0:=by
   obtain ⟨t,ht,H⟩:=hs.funding; apply receiptV; intro x y; apply hotNone; intro v; let g:=dart X x y*plume Y x y v.1
   have hh:=nu_shape p
   have he:= lettr p x y v.2; rw [show TimeA K X Y (SinB p) x y v=Oct K (plume (SinB p) x y v.2 0) g from funext fun i=> Finset.sum_congr rfl (fun u _=> mul_comm ..)]
   exact alone he ((plant _ _ hp).mool (parcelC _ _ _ hq)) hs.station ht H (by omega)
lemma allC (hs:Woody U K d)(hd:0<d)(hm:m+4=p.heat+1+1+(q.heat+1)+(t.heat+1)): Fruit U m (Triad K A (SinB p) (SinB q) (SinB t)) 0:=by
   obtain ⟨r,ht,H⟩:=hs.funding; apply receiptV; intro x y; apply hotNone; intro v
   change Fruit U m (fun i=>∑ z∈pod (K i), dart (SinB p) x y 0 z*plume (SinB q) x y v.1 0 z*plume (SinB t) x y v.2 0 z) 0
   exact thrice (lettr_step p x y) (lettr q x y v.1) (lettr t x y v.2) hd hs.station ht H (by linarith [nu_shape p,nu_shape q,nu_shape t])
end YM.OPE.Nestle
