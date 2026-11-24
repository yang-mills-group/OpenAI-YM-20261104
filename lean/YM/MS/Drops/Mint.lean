import YM.MS.Drops.Hear
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
open Next.Rank.Radian
variable {G:Gauge}
lemma press_H (s: List Axis)(φ:E4→ℂ)(t:E4): press s φ t=( s.map (fun i=>I*(ν t i:ℂ)) ).prod*φ t:= by
    induction s with | nil=> exact (one_mul ..)|>.symm| cons i s he=> change chirp i t * press s φ t = _; rw [he,List.map_cons,List.prod_cons, show chirp i t= I*(ν t i:ℂ) from (by unfold chirp; rw [phaseFπ]; unfold τ; push_cast; ring) ]; ring
variable (L K:Degree G)
lemma glow_run (p:FourP): (( List.ofFn L.layout ).reverse.map (fun i=>I*(p i:ℂ)) ).prod= GlowD L p:= by rw [ List.map_reverse, List.prod_reverse,List.map_ofFn, Fin.prod_ofFn ]; simp [ GlowD, Finset.prod_mul_distrib ]
lemma glow_spin (p:FourP): GlowD L (-p)=(-1)^L.degree * GlowD L p:= by unfold GlowD; simp only [Pi.neg_apply, Complex.ofReal_neg ]; simp_rw [ show ∀ i:Axis,-(p i:ℂ)=(-1:ℂ)*(p i:ℂ) from fun x=> (neg_one_mul _).symm, Finset.prod_mul_distrib ]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin ]; ring
abbrev Coil (k l:Axis)(i:Axis)(p: FourP):= (if i=l then I*(p k:ℂ) else 0) - if i=k then I*(p l:ℂ) else 0
lemma axis_eq (j k i:Axis)(p:FourP)(hp:j≠k): axisC j k i p = Coil j k i p:= by unfold axisC Coil; split_ifs <;> first | (solve| tauto)| (grind)
lemma axis_opp (j k i:Axis)(p:FourP)(hp:j≠k): axisC j k i (-p)= - Coil j k i p:= by rw [axis_eq j k _ _ hp]; unfold Coil; simp; split_ifs <;> ring
lemma efforts (p:FourP)(i j k l:Axis): (∑ a,Coil i j a p* (-Coil k l a p))= feather i j k l ( fun i j=> (I * (p i:ℂ)) * ( I * (p j:ℂ) ) ):= by
    let P(i:Axis):= I*(p i:ℂ); unfold Coil; simp_rw [sub_mul,mul_neg,mul_sub,Finset.sum_sub_distrib, Finset.sum_neg_distrib,ite_mul,mul_ite]; unfold feather; simp [eq_comm]
lemma front (φ:E4→ℂ) (t:E4): xy (fax L) (fax K) (ν t) * φ t=paints L K (fun i j=> press (raypath L K++[i,j]) φ) t:= by
    -- collapse color.
    let V(c:G.ColorIndex):= ∑ i:Axis, fax L ( W i c (ν t) ) * fax K ( W i c (-(ν t)) ); change (∑ c,V c)*φ t=_; rw [ Finset.sum_eq_single_of_mem L.paint (Finset.mem_univ L.paint) ]; -- change missing *
    swap; · intro b hb ht; simp only [V,photo,if_neg ht,zero_mul, Finset.sum_const_zero]
    unfold V; simp_rw [ photo ]; by_cases hp:L.paint=K.paint; swap; · simp [hp,paints]
    let i:= L.a.val.1; let j:= L.a.val.2; let k:= K.a.val.1; let l:= K.a.val.2; have he:i≠j:= (show i< j from L.a.property).ne; have hq:k≠l:= (show k<l from K.a.property).ne; let p:=ν t; let A(s:Axis):= I*(p s:ℂ); let g:=GlowD L p; let h:=GlowD K p; let T:=(-1:ℂ)^K.degree
    simp only [if_pos hp,↓reduceIte,paints,Pi.smul_apply]; change (∑ a:Axis, g* axisC i j a p*(GlowD K (-p)* axisC k l a (-p)))*φ t = _
    have hm (i j:Axis): press (raypath L K++[i,j]) φ t = g*h*(A i*A j)*φ t:= by rw [ press_H ]; unfold raypath; simp only [ List.map_append,List.prod_append,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil, mul_one, glow_run ]; unfold g h A p; ring
    simp_rw [axis_eq i j _ _ he, axis_opp k l _ _ hq,glow_spin ]
    change (∑ a,g*Coil i j a p *(( T*h )*(-Coil k l a p)))*φ t=T* feather i j k l (fun i j=> press ( raypath L K++[i,j] ) φ) t
    simp_rw [show ∀ a:Axis,g*Coil i j a p* ( (T*h)* (-Coil k l a p) )=g*h*T*(Coil i j a p* ( -Coil k l a p )) from fun a=>by ring, ← Finset.mul_sum, efforts ]; unfold feather; simp only [ Pi.sub_apply ]; split_ifs <;> simp only [Pi.zero_apply, hm ] <;> try unfold A
    all_goals ring
end YM.MS.Drops
