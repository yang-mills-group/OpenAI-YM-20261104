import YM.OPE.Compatible.Emu.World
import YM.OPE.Compatible.Navy.Poly
import YM.OPE.Compatible.Eyrie.Hill
/-!
# Chamber Haar analysis
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Set
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal
open Eyrie Push.Mark Cascade
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
noncomputable abbrev Palace (G:Gauge)(r:ℕ):= ↥(fieldP r)→ G.El
local notation "K!"=> Palace G r
local notation "F!"=> Config G n
variable (hp:Board n (r+1))
noncomputable def install (U:F!)(z:K!):F!:= fun i=>if h:i∈fringe r n then z (from_port hp i h|>.choose) else U i
@[fun_prop] lemma Cinst : Continuous (fun x:F!×K! =>install hp x.1 x.2):=by apply continuous_pi; intro i; unfold install;split<;>fun_prop
lemma monoInst (U:F!):Continuous (install hp U):=(Cinst hp).comp (f:=fun x:K! =>(U,x)) (by fun_prop) -- != spacing
lemma inF (U:F!)(z:K!)(i:Edge (Site n))(hi:i∉fringe r n): install hp U z i=U i:=dif_neg hi
lemma inSeat (U:F!)(z:K!)(i:↥(fieldP r)): install hp U z (dig hp i)=z i:=by
       let h:= ported hp i; unfold install; rw[dif_pos h,show (from_port hp _ h).choose=i from (dig hp).injective (from_port hp _ h).choose_spec]
noncomputable def move (U:F!)(z:K!):= U * install hp 1 z
lemma move_inst (U:F!)(z:K!): move hp U z=install hp U ((fun j=> U (dig hp j))*z):=by
       funext i; by_cases h:i∈fringe r n;swap;· rw[inF hp _ _ _ h];change U i*_=U i; rw[inF hp _ _ _ h];exact mul_one _
       obtain ⟨j,rfl⟩:= from_port hp i h;rw[inSeat]; change U _*install hp _ _ _= _;rw[inSeat];rfl
abbrev Duo (G:Gauge)(r:ℕ):Measure (Palace G r):= Gem G _
noncomputable def innC (φ:lots G n)(U:F!) :ℂ:=∫ k:K!,φ (install hp U k) ∂ Duo G r
private lemma plumb {E:Type}[MeasurableSpace E] (m:E→E)(μ:Measure E)(hm:MeasurePreserving m μ μ)(φ:E→ℂ)(hv:Measurable φ): (∫ i,φ i ∂μ)=∫ i,φ (m i) ∂μ:=by
       nth_rw 1[←hm.map_eq];exact integral_map hm.aemeasurable hv.aestronglyMeasurable
lemma bent (φ:lots G n)(hf:Continuous φ)(U:F!):innC hp φ U=∫ i:K!,φ (move hp U i) ∂Duo G r:=by
       let f(x:K!):K!:=(fun j=>U (dig hp j))*x
       have hm:MeasurePreserving f (Duo G r) (Duo G r):=measurePreserving_pi (f:=fun i w=>U (dig hp i)*w) _ _ fun i=> measurePreserving_mul_left G.probHaar _
       have he(v:K!) : move hp U v=install hp U (f v):= move_inst hp U v; simp_rw [he]; exact plumb f _ hm (φ∘ install hp U) ((hf.comp (monoInst hp U)).measurable)
lemma outF (x:Site n): x∈Outer r 0 ↔ r < pdist x :=by change r < pdist (x-0)↔ _;rw[sub_zero]
include hp
lemma inTent (e:Edge (Site n)): ¬(e∈mesa r n ∨ e∈fringe r n) ↔ e.1∈Outer r 0 ∧ dotUp e∈Outer r 0:=by rw[regionH _ hp];simp only [berthH,outF,not_or,not_le]
lemma private_q (U:F!)(z:K!):Agrees (Outer r 0) U (move hp U z):=fun e he hz=>by rw[move_inst,inF hp U _ _ (fun h=>(inTent hp e).mpr ⟨he,hz⟩ (Or.inr h))]
lemma innGI (φ:lots G n)(hf:Continuous φ)(hv:GaugeInvariant φ): LocalOn (Outer r 0) (innC hp φ):=by
       intro U V H; obtain ⟨s,hs,hL⟩:= Mov hp U V; let X(j:K!) : K! := fun i=> s (dig hp i|>.1) * j i * (s (dotUp (dig hp i)))⁻¹
       have he(i:K!):install hp V (X i)=Lattice.gauge s (install hp U i):=by
            funext j; by_cases h:j∈fringe r n;· obtain ⟨w,rfl⟩:= from_port hp j h; rw[inSeat];unfold Lattice.gauge; rw [inSeat]
            rw[inF hp V (X i) j h];unfold Lattice.gauge;rw[inF hp U i j h]; by_cases ht:j∈mesa r n; exact (hL _ ht).symm; obtain ⟨ha,hb⟩:= (inTent hp j).mp (not_or.mpr ⟨ht,h⟩); have hk: s (dotUp j)=1:=hs _ ((outF _).mp hb); rw [H j ha hb, hs _ ((outF _).mp ha), show s _=1 from hk,one_mul,inv_one,mul_one]
       have hX:MeasurePreserving X (Duo G r) (Duo G r):= measurePreserving_pi _ _ fun i=> (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _)
       symm; change (∫ i:K!,φ (install hp V i) ∂Duo G r)=_; rw [plumb X (Duo G r) hX (fun i=>φ (install hp V i)) (hf.comp (monoInst hp V)|>.measurable)]
       exact integral_congr_ae (Eventually.of_forall fun i=> (congr_arg φ (he i)).trans (hv s (install hp U i)))
end YM.OPE.Merchant.Aloof
