import YM.Contacts.Junction.Ghost
/-! # dual real/log lift commute: germ apparatus. Hold polynomial roots at full rank. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c f:Side}{S:StepData c f} (P : ChartRatio G) {Λ σ C e a v b:ℝ}{n k:ℕ}
namespace Cove
open Ion House Lintel Lintel.Angle
open Milling.Garf Milling.Spark Loom
variable (F:Forest S.ratio)(T: Tube G S)(j:S.Choices)
local notation "Y" => Truck G F
local notation "E" => Anchor G c
local notation "Ξ" => (ℝ×E)×Y
local notation "α" => cap G f
variable (L:Anchor G c→L[ℝ] Truck G F)
local notation "ζ" => (localL F L)
local notation "θ" => (clockF (G:=G) F)
abbrev enact (Z:ℝ → Config G f→ℝ) : α→ℝ:= fun p=> Z p.1 (input G f p.2)
def scoreP (B: α→ℝ) (x:Ξ):= ribbon P F T j L x + B (shuttle F L x)
def classic (Z:ℝ → Config G f→ℝ) : Ξ→ℝ:= scoreP P F T j L (enact Z-enact (material T.high T.up))
variable {X:House (Lines G f 1)} {Z: ℝ→ Config G f→ℝ}
local notation "ϕ" => ribbon P F T j L
local notation "λQ" => (Lapis.table F j T.up T.high)
variable (hp:T.up.Bounds T.high σ C Λ)(hg:Larger (G:=G) S) (ht:LocalRatio P) {ρ:Bid.Dir G c→ AxisChart G F}
local notation "XS" => (shuttle F L)
variable (he:Package Z X (k+3)) (hb:Package (material T.high T.up) X 5)
include he hb -- f maybe named n change
lemma epochS : Rays 3 (enact Z- enact (material T.high T.up)) := by
    let p:= enact Z; let W:=enact (material T.high T.up (f:=f)); have hp := orchestra X; apply Milling.benchPitch  (he.vest.sub hb.vest); intro x i hi; erw [jet_minus p W i (1,x) he.vest hb.vest,nightwalk (f:=p) he.vest (hp _) he.exact _ (by omega) _,nightwalk (f:=W) hb.vest (hp _) hb.exact _ (by omega) _,swell_front X (k+3),swell_front X 5,if_pos (by omega), if_pos (by omega),sub_self]
include hp hg ht
omit hb he in
lemma enamel {B:cap G f→ℝ} (h:AnalyticAt ℝ B 0) (hE:Rays 3 B) : let v:= scoreP P F T j L B; AnalyticAt ℝ v 0 ∧ ∀ x i,i≤2→ jet v i x=jet λQ i (ζ x):= by
    intro V; let u:=ζ; let w:=B∘ XS; have hw:AnalyticAt ℝ w 0:= AnalyticAt.comp (f:=XS) (x:=0) (by rw [shuttle0];exact h) (shuttleH F L); refine ⟨(ribbonH P F T j L hp hg ht).add (g:=w) hw,fun x i hi=>?_⟩; change jet (ϕ+w) i x= _; rw [serif (ribbonH P F T j L hp hg ht) _ hw,ribbon_low P F T j L hp hg ht hi,(jet_bridge hw).mp (merkin h hE XS (shuttleH F L) (shuttle0 F L)) x i (by omega),add_zero] -- f= notation?
lemma estate : let v:= classic P F T j L Z; AnalyticAt ℝ v 0 ∧ Measurable v ∧ ∀ x i,i≤2 → jet v i x=jet λQ i (ζ x):= by
   obtain ⟨hs,h⟩:= enamel P F T j L hp hg ht (he.vest.sub hb.vest) (epochS T he hb);
   let B:=enact Z-enact (material T.high T.up); let l i:=B (XS i); intro v; refine ⟨hs,?_,h⟩; let u:=fun x:α=>(x.1,input G f x.2); have hW:Continuous XS:= continuous_iff_continuousAt.mpr fun i=> by unfold shuttle; exact ((θ).continuous.continuousAt.prodMk ((laneH _).continuousAt.comp (f:=ζ) (ζ).continuous.continuousAt));
   refine ((ribbon_caps P F T j L hp hg ht).add (g:=l) ?_); apply Measurable.comp (he.paid.sub hb.paid) (f:=u ∘ XS); exact (continuous_fst.prodMk ((input_cont (G:=G) (m:=f)).comp continuous_snd)).measurable.comp hW.measurable -- continuous_fst
local notation "R₀" => runner (visitor S Z) F
local notation "hn" => Fintype.card F.Free
local notation "ε" => P.scale^Fintype.card F.Free
omit hb
open Milling.Forge
lemma hymn : let V:=classic P F T (Milling.Garf.art S) L Z; ∀ᶠ z: Ξ in 𝓝 0,z.1.1>0 →
       YM.Next.SectorChange.pay P (Fare.windmill F (L z.1.2+z.2)) * R₀ (z.1.1,settle c z.1.2) (om F (ζ z))= ε *Real.exp (-V z/z.1.1^2) := by
    let V:=classic P F T (art S) L Z; intro q; have h : Tendsto ζ (𝓝 0) (𝓝 0):=(ζ).map_zero ▸ (ζ).continuous.tendsto 0; let fE:=pul F ∘ ζ; have hp:Tendsto fE (𝓝 0) (𝓝 1):= ((pul0 F) ▸ (pulH F (G:=G)).tendsto 0).comp h;  -- notation Y conflict
    let p:=Fare.windmill F (G:=G); have hW:Tendsto (p ∘ Prod.snd ∘ ζ) (𝓝 0) (𝓝 0):= ((wind0 F) ▸ (paintH F (G:=G)).tendsto 0).comp (continuousAt_snd.tendsto.comp h); have hx: mouth P∈ 𝓝 (0:LogArray G F.Free):= (show mouth P=ball (0:LogArray G F.Free) P.radius from (ball_pi _ ht.patch).symm) ▸ Metric.ball_mem_nhds _ ht.patch
    filter_upwards [hp.eventually (Forge.ground_deduct hg.1),hW.eventually (show ∀ᶠ y in 𝓝 (0:LogArray G F.Free), y ∈ mouth P from hx), h.eventually (mintL F)] with z hμ hx hZ hz; let t:= z.1.1; let w:= ζ z; let sr:=Lapis.sumAt F P w.2; let b:=noiseTaylor S (ship z.1.2) (fE z) (art S); let y:=Z t (fE z)
    have hw: V z= y+b-t^2*sr := by
        have h:enact Z (XS z)=y:= by change Z t (input G f _)=y; unfold y; change Z t ((input G _) (lane F w))= _; exact congr_arg (Z t) hZ
        have hl:enact (f:=(by exact f)) (material T.high T.up) (XS z)= material T.high T.up t (fE z):= congr_arg (material T.high T.up t) hZ
        unfold V classic scoreP; rw [Pi.sub_apply,h,hl]; change (mainTerm T.high T.up (fE z)+b+t^2*(Precision.loop T.up (fE z)-sr))+ (y-(mainTerm T.high T.up (fE z)+t^2*Precision.loop T.up (fE z)))=_; ring
    rw [ray_meter P F ht (L z.1.2+z.2) hx]; change (P.scale^ hn *Real.exp sr)* (Forge.visitor S Z t (fE z) (ship z.1.2)) = ε * Real.exp (-V z/z.1.1^2); rw [hw, mul_assoc,Forge.visitor,hμ (ship z.1.2)]; let E':= -(t^2)⁻¹*b; change _* (Real.exp sr*(Real.exp E'*Real.exp (-y/t^2)))= (P.scale^ hn)*Real.exp (- (y+b-t^2*sr)/ _); rw [← Real.exp_add,← Real.exp_add]; apply congr_arg; apply congr_arg; unfold E'; change _ = _ / (t^2); have hh:0<t:=hz; field_simp; ring
-- furniture.Books
lemma lore_cap {G0:cap G c→ℝ}(hh: Sight R₀ G0 b k)(x:E)(u:ℝ)(hu:0<u): let V := classic P F T (art S) L Z; ∃ r>0,r < u ∧ ∃ Q:ℝ→Set Y,(∀ᶠ t in Tested.germ, MeasurableSet (Q t) ∧ disc t r⊆ Q t ∧ Q t⊆ disc t u) ∧ Tested.Bill (k+1) (fun t=> ash volume 1 V t (Q t) (1,x)- (b / (P.scale^hn))*Radial.projection 1 G0 t (1, settle c x)):= by intro V; refine playing F L hh ht (fun x=>((visit_meas (S:=S) he hg.1 x.1 _).comp (F.continuous_drape.measurable)).stronglyMeasurable) (pow_pos ht.scale _) (hymn P F T L hp hg ht he) x u hu -- param q
include hb
-- per-torus reach
lemma bears {G0:cap G c→ℝ}(hh:Sight R₀ G0 b k) {B:Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)} (hx:B.Service F T.high T.up ρ) (hU:Radial.Stationary G0) : let q:=seam F ρ; let V :=classic P F T (art S) q Z; Radar.Alive volume (Poll.sweep (Lapis.gram F T.up T.high ρ (art S) 0)⁻¹) (settle c) V G0 (camber (Lapis.table F (art S) T.up T.high) q) k:= by
    let q:= seam F ρ; let p:= Lapis.table F (art S) T.up T.high; let S' := Lapis.gram F T.up T.high ρ (art S) 0; have hM:= (Lapis.wakes F (art S) T.up T.high ρ _ _ _ B hg hp hx 0 (by rw [norm_zero]; exact hx.x_pos)).1;
    let d:= Junction.law S'; let J:= camber p q; have hd : 0<d:= inv_pos.mpr (Shield.fullFuel ..); let V:= classic P F T (art S) q Z; obtain ⟨hA,hZ,hR⟩:= estate P F T (art S) q hp hg ht he hb;
    let g:=V; let P₀:=Lapis.gram F T.up T.high ρ; let f x:= Radar.beats g x; -- maybe some unresolved implicit
    have hw (x:ℝ×E)(y:Y): jet V 2 (x,y)=J x.2 + Junction.gram F S' y:= by
        let w: E×Y:= (x.2,y); rw [show jet V 2 _= _ from hR (x,y) 2 (by norm_num)]; change jet p 2 ((levelL q) w)= _; rw [show jet p 2 ((levelL q) w)=jet (p ∘ (levelL q)) 2 w from (Milling.Garf.woven (F:=p) (kernelCost F T (art S) hp hg).1 (levelL q) w _).symm] -- ← wrong
        exact cleavage F T (art S) hx hp hg x.2 y
    intro q' U; refine ⟨pillow (F:=V) (u:=J ∘ Prod.snd) (Q:=Junction.gram F S') hA (cam_zero F T (art S) q) (Junction.gram_pos F _ hM) hw,?_, ⟨⟨hA.contDiffAt, ?_,fun i=>?_⟩,hU,hZ⟩⟩ -- n goals order
    · refine ⟨d,hd,b/ε, div_pos hh.nz (pow_pos ht.scale _), fun x i=>?_, lore_cap P F T q hp hg ht he hh⟩; unfold Milling.mural Radar.spectrum normTerm; rw [Blaze.Shield.recommends _ hM.inv, ← integral_const_mul]; apply integral_congr_ae; filter_upwards with z; rw [Milling.unclad]; change Radar.beats V _ _ * Real.exp (-jet V 2 _) = _; rw [hw,neg_add,Real.exp_add,Junction.lens F _ hM]; dsimp only; change _ = (d * Real.exp (-J x)) * (Shield.lens₀ _ z * Radar.beats V _ _); unfold d; ring
    · exact (jet_zero V 0).symm.trans ((hR 0 0 (by norm_num)).trans ((jet_zero ..).trans (kernelCost F T (art S) hp hg).2.base0))
    exact (hR i 1 (by norm_num)).trans ((kernelCost F T (art S) hp hg).2.base1 _)
end Cove
end YM.Contacts.Junction
