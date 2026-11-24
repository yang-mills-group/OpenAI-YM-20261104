import YM.SchemeConversionRG11.FirstW.Trice.Locale
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped Topology ContDiff BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side} {G:Gauge}{s t u:StepPath T} {A B C:Sight T G} {p q r: Axis→E4→G.Color}{x y z:E4}{R:ℝ}{S:Set E4}
def ack (T:Itinerary)(A B C:Sight T G)(i j a b:Axis): Hall T ℝ:= fun l x=>inner ℝ (ray i (stalkH T A j) l x) (claw T B C a b l x)
def vst (p q r: Axis→E4→G.Color)(i j a b:Axis)(x:E4):= inner ℝ (grad i (p j) x) (pitch q r a b x)
lemma lift_ack (A B C:Sight T G)(x:StepPath T)(i j a b:Axis): slipU T x (ack T A B C i j a b) =ack T (passA T x A) (passA T x B) (passA T x C) i j a b := by
 funext k t; change inner ℝ (slipU T x (ray i (stalkH T A j)) k t) (slipU T x (claw T B C a b) k t)=_; rw [slip_ray,stalk_shift,rise_jet];rfl
-- direct words with three marked, differentiated on first
section stars
variable {A₀ B₀ C₀:Badge G}{b₁ b₂ b₃:Bool} (i j a b:Axis)
local notation "L1" => Laurel A₀ b₁ T s
local notation "L2" => Laurel B₀ b₂ T t
local notation "L3" => Laurel C₀ b₃ T u
local notation "A1" => toast A₀ b₁ x
local notation "A2" => toast B₀ b₂ y
local notation "A3" => toast C₀ b₃ z
lemma ack_limit (hx:sails T s x)(hy:sails T t y)(hz:sails T u z)(hs:S⊆{v|v≠x})(ht:S⊆{v|v≠y})(hv:S⊆{v|v≠z})(hc:MarkGrid T c) : Meets T S (ack T L1 L2 L3 i j a b) (vst A1 A2 A3 i j a b):=by
 have H : Meets T S (ray i (stalkH T L1 j)) (grad i (A1 j)) := (matched (send_all A₀ b₁ j hx) (isOpen_ne_fun continuous_id continuous_const) i (laurel_scans _ _ _ hx _) hc (fun _ hw=>(toast_diff A₀ _ i j hw).1)).restrict hs
 exact H.price (clawV (q:=A3) (p:=A2) (fun i=> (send_all _ _ i hy).restrict ht) (fun i=>(send_all _ _ i hz).restrict hv) a b) (fun x y=>inner ℝ x y) (show Continuous (uncurry (fun (x y:G.Color)=>inner ℝ x y)) from continuous_inner)
abbrev Absent (x y z:E4) : Set E4:=({u|u≠x} ∩{u|u≠y}) ∩ {u|u≠z}
lemma missing : Absent x y z ∈ ae volume:= inter_mem (inter_mem (volume.ae_ne x) (volume.ae_ne y)) (volume.ae_ne z)
variable {P:Hall T ℝ}{P':E4→ℝ}
lemma bead_limit (hx:sails T s x)(hy:sails T t y)(hz:sails T u z)(hw:Meets T univ P P')(hc:MarkGrid T c): Meets T (Absent x y z) (P*ack T L1 L2 L3 i j a b) (P'*vst A1 A2 A3 i j a b):=meets_goods (hw.restrict (subset_univ _)) (ack_limit _ _ _ _ hx hy hz (fun _ h=>h.1.1) (fun _ h=>h.1.2) (fun _ h=>h.2) hc)
lemma high_seat (hx:sails T s x)(hy:sails T t y)(hz:sails T u z)(Hw:Meets T univ P P')(hp:Gloam T P 0 P)(he:Leeway T s P)(ht:Leeway T t P)(hu:Leeway T u P)(hc:MarkGrid T c): Market T (P*ack T L1 L2 L3 i j a b) (P'*vst A1 A2 A3 i j a b) := by
 let f:= ack T L1 L2 L3 i j a b
 have h: Gloam T P 6 (P*f):= by
   have hh: Gloam T P 2 (ray i (stalkH T L1 j)):= Gloam.settle he hx (extra_shore _ _ _ _ _) (by decide)
   have hv: Gloam T P 4 (claw T L2 L3 a b):= spire_boundG ht hy (ShoreD ..|>.1) (by decide:2≤3) hz hu (ShoreD ..|>.1) (by decide:2≤3) _
   exact hp.map₂ (hh.map₂ hv (innerSL ℝ)) (ContinuousLinearMap.mul ℝ ℝ)
 obtain ⟨D,hD,H⟩:=h
 have e:∀ᵐ x∂volume,x∈Absent _ _ _:= missing (x:=x) (y:=y) (z:=z)
 have hh:= bead_limit i j a b hx hy hz (A₀:=A₀) (B₀:=B₀) (C₀:=C₀) (b₁:=b₁) (b₂:=b₂) (b₃:=b₃) Hw hc
 apply outlast (f:=P*f) _ (e.mono fun v hv p hp=>hh id tendsto_id v hv _ hp) hD.le hc
 refine H.mono fun k hk x=>?_; by_cases h:P k x=0; · simp [h,hD.le]
 exact hk x h
lemma local_seat (Q:Wash)(hx:sails T s x)(hy:sails T t y)(hz:sails T u z)(hr:Q.rOut<‖x-y‖)(he:Q.rOut<‖z-y‖)(h:Meets T univ P P')(hc:MarkGrid T c):
 Market T (Mask T t Q*P*ack T L1 L2 L3 i j a b) (blot Q y*P'*vst A1 A2 A3 i j a b) := by
 let V: Set E4:= (fun x=>x+y) ⁻¹' (Absent x y z); let Qp:= Mask T t Q*P; let q:=ack T L1 L2 L3 i j a b
 have hb:= bead_limit (A₀:=A₀) (B₀:=B₀) (C₀:=C₀) (b₁:=b₁) (b₂:=b₂) (b₃:=b₃) i j a b hx hy hz (meets_goods (mask_meet Q hy) h) hc
 have ht:= hb.quote t hy V (fun _ h=>h); have heq: slipU T t (Qp*q)= (Mask T 0 Q*slipU T t P)*ack T (Laurel A₀ b₁ T (s-t)) (Laurel B₀ b₂ T 0) (Laurel C₀ b₃ T (u-t)) i j a b:= by
    rw [show slipU T t (Qp*q)=(resiteR T (Mask T t Q) t*slipU T t P) * slipU T t q from rfl];unfold q; rw [lift_ack,resite_mask,sub_self,statue,statue,sub_self,statue]
 have ha: Town Q.rOut ⊆ {v:E4|v≠ x-y}:=blotted hr; have hd : Town Q.rOut⊆{v:E4|v≠z-y}:= blotted he
 apply Market.move t (v:=y) -- placeholder
 apply holdsLocal (R:=Q.rOut) (S:=V) _ _ _ hc ht
 · change Camper T Q.rOut 3 (slipU T t (Qp*q));rw [heq]
   let A' := Laurel A₀ b₁ T (s-t); let B':= Laurel B₀ b₂ T 0; let C':= Laurel C₀ b₃ T (u-t)
   have h₀:= spire_camp ((ShoreD 0 B₀ b₂).1) (laurel_scans C₀ b₃ _ (sails_sub hz hy)) a b hd
   obtain ⟨S,H⟩:= laurel_scans A₀ b₁ _ (sails_sub hx hy) j
   have h₁:=campers (f:=ray i (stalkH T A' j)) (H [i]) ha; have hb:= meets_goods (mask_meet Q (sails_zero (T:=T))) (h.quote _ hy univ (fun _ _=>mem_univ _))
   exact campers_prod (campers (f:=Mask T 0 Q*slipU T t P) hb (subset_univ _)) (campers_prod h₁ h₀ (innerSL ℝ)) (ContinuousLinearMap.mul ℝ ℝ)
 · change Placed T Q.rOut (slipU T t (Qp*q)); rw [heq]; exact Eventually.mono (mask_placed Q) fun i hi x hx=> hi x (fun h=> hx (by simp [h]))
 have hz(p:E4): ∀ᵐ v: E4 ∂volume,v+y≠p:=by filter_upwards [volume.ae_ne (p-y)] with v hv w; apply hv; exact eq_sub_of_add_eq w
 exact Eventually.mono (((hz x).and (hz y)).and (hz z)) fun _ u=>u
-- similarly for z by symmetry claw
lemma turn_ack (A B C:Sight T G): ack T A B C i j a b=ack T A C B i j a b:= funext fun m=>funext fun z=>by rw [ack,claw, spire_comm]; rfl
lemma turn_p (A B C:Axis→ E4→ G.Color) : vst A B C i j a b=vst A C B i j a b := funext fun x=> by unfold vst pitch; rw [ad_for (B a x) (C b x),ad_for (B b x) (C a x)]; apply congrArg _; abel
lemma exterior_budget (Q W:Wash)(hx:sails T s x)(hy:sails T t y)(hz:sails T u z)(hr:Q.rOut<‖x-y‖)(hxy:Q.rOut<‖z-y‖)(he:Q.rOut<‖x-z‖)(hc:MarkGrid T c): Market T ((1-Mask T s W)*ack T L1 L2 L3 i j a b) ((1-blot W x)*vst A1 A2 A3 i j a b) := by
 let U:= Mask T t Q; let V := Mask T u Q; let X:Hall T ℝ:=1-Mask T s W
 let U':= blot Q y; let V':= blot Q z; let X':= 1-blot W x
 let P:= (1-U)*X; let P':=(1-U')*X'; let D:= (1-V)*P; let D':= (1-V')*P'; let q:= ack T L1 L2 L3 i j a b; let q':=vst A1 A2 A3 i j a b
 have h1:Market T (U*X*q) (U'*X'*q'):= local_seat i j a b Q hx hy hz hr hxy (meets_ice W hx) hc
 have hP:Meets T univ P P':= meets_goods (meets_ice Q hy) (meets_ice W hx); have hQ: Market T (V*P*q) (V'*P'*q'):= by unfold q q';rw [turn_ack, turn_p]; exact local_seat i j a b Q hx hz hy he (by rwa [norm_sub_rev]) hP hc
 have he1:=waymore (V:=D) (iced_way s W) fun i x hx=> fun h=> hx (by simp [D,P,X,show 1-Mask T s W i x=0 from h]); have he2:= waymore (V:=D) (iced_way t Q) fun i x hx=> fun h=> hx (by simp [D,P,U,show 1-Mask T t Q i x=0 from h]); have he3:= waymore (V:=D) (iced_way u Q) fun i x hx=> fun h=> hx (by simp [D,V,show 1-Mask T u Q i x=0 from h])
 let L:= ContinuousLinearMap.mul ℝ ℝ; have hm:Market T (D*q) (D'*q'):= high_seat i j a b hx hy hz (meets_goods (meets_ice Q hz) hP) (show Gloam T D 0 D from (ara _ _).map₂ ((ara _ _).map₂ (ara _ _) L) L) he1 he2 he3 hc
 have hv:=h1.plus hQ|>.plus hm; change Market T (X*q) (X'*q'); convert hv using 1
 · unfold D P; ring
 unfold D' P'; ring
end stars
end YM.RG11.FirstW
