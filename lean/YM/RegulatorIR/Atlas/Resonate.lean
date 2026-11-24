import YM.RegulatorIR.Atlas.Outfit

/-!
# Cover data irrespective of periods and extra coarser steps

Extent alignment via Section. Beta gauges at a pivot using the same
color representative determine values on aligned interval without
assuming downstream cost caps. Never applies to orbit coefficients;
orbit comparison uses the INDEPENDENT size-sensitive diagram compute.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Atlas
open Function Filter Finset Budget Uniform
open Lattice RG Gauge Prim Binding Epoch Epoch.League Geometry Step Taping Precision Oracle Venture Laurent Bloch Halo Profiles Calibration Momentum
open YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky
open Ward Clocks Exterior PertExtension Series Series.Radial Series.Tested Quadratic
open scoped ENNReal NNReal Topology BigOperators Classical
variable {X Y I J:Type}{M:X→ℕ}{N:Y→ℕ}{m:Page M→ Side}{n:Page N→Side}
private lemma lap_none (V:Layer I J): lap (0:Layer I I) V=0:=by ext1 x;ext1 y;simp [lap]
private lemma lap_sans (V:Layer I J):lap V (0:Layer J I)=0:=by ext1 x;ext1 y;simp [lap]
variable {K:KernelChoices}(S:Circuit M m)(G:Gauge)(R:Program K)(Z:∀ P:Patch,P.Branches K G)(T:Circuit N n)
variable {p:ℕ} (U:Section S T) (H:∀ w,U.connects (Page.opening M w)=Page.opening N (U.cast_r w))
local notation "L"=> S.payroll R G Z
local notation "L'"=> T.payroll R G Z
local notation "C"=> U.connects
local notation "c₁"=> S.scroll_j R G
local notation "c₂"=> T.scroll_j R G
local notation "C₀"=>U.cast_r
include H
lemma accedes : ∀ i,c₁ i= c₂ (C i):=by
 refine Page.proves (fun w=>by rw [H,S.crust_top,T.crust_top]) ?_
 intro i hx
 let b:=U.fly i
 rw [U.previous] at hx; rw [U.next];apply sub_eq_zero.mp
 have he : ∃ W:Cross (S.pactP i).L (TypeFace 1) (TypeFace 1), BidP (S.pactP i) K (T.tables R b.prev) (T.tables R b.next) W (R.receipt.α (T.J b.prev)) (lesser (R.receipt.Ω (T.J b.prev)) (T.sizeL b)):=by rw [← U.pact]; exact ⟨T.tells R b,T.predicted R b⟩
 obtain ⟨W,hp⟩:= he
 change crust _ _- crust _ _=0
 rw [upwards G K (S.pactP i) _ _ (S.honored R i.prev).card (S.honored R i.next).card (T.honored R b.prev).card (T.honored R b.next).card (S.predicted R i) hp, show crust _ _ - crust G (T.tables R b.prev)=0 from sub_eq_zero.mpr hx, lap_none, lap_sans]
lemma sharing (i:Flap M) : S.pulses R G Z i=T.pulses R G Z (U.fly i) ∧ S.sails R G i=T.sails R G (U.fly i):=by
 have he:= sub_eq_zero.mpr (accedes S G R T U H i.prev)
 exact ⟨sub_eq_zero.mp (by rw [pulse_motion Z U i,he,neg_zero,lap_none,lap_sans]),sub_eq_zero.mp (by rw [wing_motion Z U i,he,neg_zero,lap_none,lap_sans])⟩ -- param order

variable {u:Page M→Scale}{v:Page N→Scale}
lemma grainS (i:Flap M) (h:Squares p (tale (u i.prev).beta) (tale (v (C i.prev)).beta)) : GridM (S.devices R G Z u i) (T.devices R G Z v (U.fly i)) p:=by
 let w:= U.fly i; rw [U.previous] at h; obtain ⟨hp,ht⟩:= sharing S G R Z T U H i
 constructor
 · exact congr_arg (petals (I:=Foot G)) hp
 · exact congr_arg swap (congr_arg hoses ht)
 intro j hj; let Kr:= S.bore G Z u i;let Kr':= T.bore G Z v w
 have hx(k): Kr k j= Kr' k j:=prism_now (S.rail K i) (T.rail K w) _ _ (U.pact i|>.symm) rfl (Z (S.pactP i)) (S.wheeled G Z u i) (T.wheeled G Z v w) h k j hj
 change many Kr j=many Kr' j; ext1 r;ext1 x;unfold many massive; exact tsum_congr fun d=>congr_fun (congr_fun (hx d) r) x

lemma neurons (h: ∀ i,Squares p (tale (u i).beta) (tale (v (C i)).beta)):∀ i:Page M, Matches p ((L u).bulk i) ((L' v).bulk (C i)):=by
 refine Page.proves ?_ ?_
 · intro w;let i:=Page.opening M w;let j:= C₀ w
   have he:= h i; rw [show C i=Page.opening N j from H w] at he;rw [H]
   intro e ht
   have hp(z) : Circuit.mural G u w z e=Circuit.mural G v j z e:= stageM (Circuit.serene G u w z) (Circuit.serene G v j z) (fun x=> plain_agree _ _ he x z) e ht
   change many _ _=many _ _; ext1 r;ext1 x;unfold many massive; exact tsum_congr fun d=> congr_fun (congr_fun (hp d) r) x
 intro i hv; rw [U.previous] at hv;rw [U.next,←(L u).step_v,←(L' v).step_v]; exact (grainS S G R Z T U H i (h _)).log_step hv
variable (c:G.ColorIndex) {D:Choice M}{D':Choice N}
lemma alike (h: ∀ w,C (D.choose w)= D'.choose (C₀ w)){u':Tent M}{v':Tent N} (hp:Notebook S R G Z c D u' p)(ht:Notebook T R G Z c D' v' p): (∀ i,Squares p (tale (sheet u' i|>.beta)) (tale (sheet v' (C i)|>.beta)))∧∀ i,Matches p ((L (sheet u')).bulk i) ((L' (sheet v')).bulk (C i)):=by
 let w:Tent M:= fun i=>v' (C i); let t:= sheet w
 have hv(i): t i=sheet v' (C i):=rfl
 have hx:= neurons S G R Z T U H (p:=p) (u:=t) (v:=sheet v') fun i=>by rw [hv];exact fun _ _=>rfl
 have hh: Notebook S R G Z c D w p:=by
    refine ⟨fun i=>⟨fun j hj hf=>?_,(ht.clean _).2⟩,fun i=> show v' _=_ from (congr_arg v' (h i)).trans (ht.reference (C₀ i))⟩
    change Pupil.Rules.token ((L t).bulk i _ _) c= _
    rw [hx i j hj]; exact (ht.clean _).1 j hj hf
 have he(i): Squares p (tale (sheet u' i|>.beta)) (tale (sheet v' (C i)|>.beta)):= recognized S R G Z c hp hh i
 exact ⟨he,neurons S G R Z T U H he⟩
end YM.RegulatorIR.Atlas
