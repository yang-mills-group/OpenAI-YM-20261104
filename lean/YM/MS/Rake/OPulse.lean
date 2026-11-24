import YM.MS.Rake.Rack
/-!
# smallest separation may be nonunit. For the same objective. Harmonic ν factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Job
open scoped Topology ContDiff
variable {G:Gauge}{ι E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{S:Scale ι}
    {T:ℝ}{x y a z v:ι→ℝ}{A:ι→QP}{X Y:ι→ Law G}{K:ι→ Edge G}
lemma PulseQ (hk:Sheet S a K)(hx:Lease false true S X x)(hy:Lease false true S Y y)(ha:nn a)(hL:nn x)(hR:nn y)
    (hb:∀ i,0<v i)(hA:∀ i,T*v i≤ ‖A i‖)(ht:∀ i,S.length i≤v i)
    (hc:paid S (fun i=>‖A i‖) v)(hT:0<T) (k:ℕ): Lease false false S (fun i=> Cabin ( A i ) (K i) planeF (X i) (Y i)) (fun i=> a i*(x i*y i)*( S.length i/v i)^k ) := by
   let c i:= S.length i/v i; have hv i:0<c i:= div_pos ( S.pos i ) (hb i); have hz i:c i≤1:= ( div_le_one (hb i)).mpr (ht i);
   refine cab_cost (μ:=fun (_:ι)=>planeF) (fun E _ _ l r w hW=>?_); let U i:= S.length i ^ pitch w*(a i*(x i*y i)); rw [ show Qbud w S _=(fun i=>U i*c i^k) from funext fun i=> (mul_assoc ..).symm]; refine pulseCost (net l) (g:=fun i (_:E)=>U i) ?_ hv hz ?_ k; swap; · unfold c; convert paid_at hc (E:=E) (fun i=>(hb i).le) using 1; ext i; field_simp [(S.pos i).ne',(hb i).ne']
   intro k; refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=>?_) ?h0) ?h0; swap; · exact fun i _ _=>mul_nonneg ( pos_nn _ (joy ha (joy hL hR)) S i ) ( pow_nonneg (hv i|>.le) _)
   have hh := large (w:=fun i=>T*v i) (fun i=> mul_pos hT (hb i)) hA ( fun i=>by simpa only [ inv_mul_cancel_left₀ hT.ne'] using (ht i)) (inv_nonneg.mpr hT.le) (meshC hk i j hW hx hy) k
   refine hh.raise ⟨ (T^k)⁻¹,inv_pos.mpr ( pow_pos hT _),0,fun i w' _=>?_⟩; unfold Qbud c positive Snap.fee U; simp only [ Pi.mul_apply, pow_zero,mul_one]; apply le_of_eq; rw [show S.length i / (T*v i)= T⁻¹ * ( S.length i/v i ) by ring,mul_pow (T⁻¹:ℝ), inv_pow ]; field_simp [(S.pos i).ne',(hb i).ne', hT.ne']
end YM.MS.Latch
