import YM.RegulatorIR.Epoch.Tariffs

/-! Slice inverse & mean births from ledger K. Real. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Epoch
open Function Set Filter Finset Lattice RG Gauge Budget Budget.Packet Budget.Tuple Budget.Layer Geometry Uniform YM.RegulatorIR.Ledger Step Taping Precision Laurent Bloch Oracle Quadratic ENNReal Exterior
open RegulatorIR.Momentum (lapL lapR lap_tools)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y I:Type}{U: X→Type}{M:X→ℕ}{P t:Page M→Side}{u p r:ℕ}
variable (G:Gauge){K: KernelChoices}
section rails
variable (W: Patch){B B' D:Bed}{C: Clip} {C':Clip} {σ α τ θ β Ω Ω' δ:ℝ} (H: Hall B σ Ω α C)(h:W.Branches K G)
local notation "N"=> hearth W K G B H h
local notation "L"=> pension W G
lemma pension_t : Function.swap (pension W G)= (pension W G):=by
 -- direct
 funext i j
 by_cases h:i=j
 · subst i; rfl
 simp [Function.swap,pension,h,Ne.symm h]
include H
lemma hard_t : Function.swap (stableK W K G B)=stableK W K G B:=by
 ext1 i;ext1 j;change crust G B j i + _=crust G B i j+_
 rw [show crust _ B j i=_ from congr_fun (congr_fun (symmetry_h G B H.floorP H.pos.le H.paid H.stripP.2.1) i) j]; apply congr_arg;apply congr_arg (fun z:ℝ=>K.penalty*z); exact tsum_congr fun _=>mul_comm ..
variable (V : Hall B' τ Ω' θ C')
local notation "N'"=>hearth W K G B' V h
lemma generates : lap N L=N ∧ lap (lap N (stableK W K G B)) L=L:=by
 obtain ⟨he,hv⟩:= crown W K G B H h; let q:=stableK W K G B
 have hx: Function.swap L=L := pension_t G W
 have ht:=congr_arg Function.swap he; have hh:= congr_arg Function.swap hv
 rw [lap_flip,lap_flip,hx, hard_t G W H, t_warm W K G B H h] at ht
 rw [lap_flip,hx,t_warm W K G B H h] at hh
 exact ⟨hh,ht⟩

lemma heat_seed : N-N'= lap N (lap (crust G B' - crust G B) N') :=by
 let D:= stableK W K G B; let F:= stableK W K G B'; let x:=hearth W K G B' V h; let v:=stableK W K G B
 obtain ⟨hv,hV⟩:= generates G W H h; obtain ⟨h',hx⟩:= crown W K G B' V h
 have hU := heatP W K G B H h; have hm:=heatP W K G B' V h; have hK:=lifetimeK W K G B H;have hM:=lifetimeK W K G B' V
 have hc: crust G B' - crust G B= F-D:=by unfold D F stableK stableL; abel
 rw [hc,lapL hM hK hm,lapR hU (hK.lap hm) (hM.lap hm)] -- arg order?
 have hb : lap N (lap F x)=N:=by
    nth_rw 1 [← hv]; rw [← lap_tools hU (savings W G) (hM.lap hm),show lap L (lap _ _)=L from h',hv]
 rw [hb,lap_tools hU hK hm]; apply congr_arg; set V':= lap N _; change x = lap V' x
 calc
   _=lap L x:=hx.symm
   _=lap V' (lap L x):=by rw [lap_tools (hU.lap hK) (savings W G) hm,hV]
   _=_:=by rw [hx]

include V
lemma diff_sail {C'' C₁:Clip}{D':Bed} {a b c e f g x y:ℝ} (hD: Hall D a b c C'')(hD':Hall D' e f g C₁)(T T' : Cross W.L (TypeFace 1) (TypeFace 1))(hp:BidP W K B D T σ x)(ht: BidP W K B' D' T' τ y): projectionQ W K T G-projectionQ W K T' G=lap N (lap (crust G B'-crust G B) (projectionQ W K T' G)):=by
 let d:= stableK W K G B;let d':=stableK W K G B'
 let Z:=projectionQ W K T G;let u:=projectionQ W K T' G
 have he:= ministry W K G B D T H hp; have hx:= ministry W K G B' D' T' V ht
 have hc:= (overrides W K T G hp.rows H.pos.le hp.costV).buys H.pos.le|>.1
 have hr:= (overrides W K T' G ht.rows V.pos.le ht.costV).buys V.pos.le|>.1
 have hb: crust G B' - crust G B= d'-d:=by unfold d d' stableK stableL; abel
 have hκ:=heatP W K G B H h; have hQ:= lifetimeK W K G B' V;have hq:= lifetimeK W K G B H; obtain ⟨hq',h'⟩:= generates G W H h
 rw [hb, lapL hQ hq hr, lapR hκ (hq.lap hr) (hQ.lap hr), show lap d' u=lap d Z from (marches W K G B' D' T' V hD' ht).1.trans ((marches W K G B D T H hD hp).1).symm]
 have he' (L':Layer (Long G.ColorIndex) (Long G.ColorIndex)) (hl:Quadratic.Billed L')(hv:lap L L'=L') :lap N (lap d L')=L':=by
    rw [lap_tools hκ hq hl]; nth_rw 1 [← hv]; rw [lap_tools (hκ.lap hq) (savings W G) hl,h', hv]
 rw [he' Z hc he, he' u hr hx]
end rails
end YM.RegulatorIR.Epoch
