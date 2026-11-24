import YM.MS.Tone.Charges
/-!
# Momentum routing in translation-equivalent functionals

Use one no-loop force formula avoiding infinite root. Signs from unrestricted Q.
    Pulse at rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone
open Function Filter Set Finset Plane Koszul Cylinder Lab Lattice Native Bare Focus Landau Momentum Paint Color Flux
open Draft
open scoped Topology ContDiff
variable {G:Gauge}
variable (F H:(Dot G Cover))
lemma route_force (i:(Branch G Axis))(x:Cover)(l:List (LightMode G QP)): run (force i x F) l=bill (net l) (bornv (i,x))*run F ((i,-net l)::l):= by
    obtain ⟨s,hs⟩:=obliges F; simp only [force_at F hs,map_sum,Finset.sum_apply,movement,grows F hs,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [opp,← inverse,← _root_.mul_assoc,← rightadd]; -- direction
    unfold bornv; rw [emb_sub]; have he: embed x+ offset i.1 + -(embed k+offset i.1)=embed x-embed k:= by abel
    rw [he]
local notation "A"=>allocate Draft.DotFlip

def knob (g h:(Score G Axis QP))(a b:(Branch G Axis))(l r:Legs (LightMode G QP)):ℂ:= cross (parity b) (degree (field parity) l) * g ((a,-net l)::l) * h ((b,net l)::r) +
     cross (parity a) ((parity b).xor (degree (field parity) l))*g ((b,-net l)::l)*h ((a,net l)::r)
lemma bulb (i j:(Branch G Axis))(hn:offset i.1=offset j.1)(l:Legs (LightMode G QP)): run (root parity i j F H) l=A l (knob (run F) (run H) i j):= by
    obtain ⟨s,hs⟩:=obliges H
    rw [root_at F H _ _ hs,map_sum,Finset.sum_apply]; simp_rw [spot_eq,map_add,wave_cost,Pi.add_apply, show ∀ f g:(Score G Axis QP), product DotFlip f g l=A l (fun a b=> f a*g b) from fun f g=> scattered ..,← map_add, ← map_sum]; congr! 1;
    -- ext under X
    funext a b; simp only [Finset.sum_apply,Pi.add_apply,run_twist,route_force,at_sign,degree_cons, knob]; simp_rw [grows H hs]; -- double phase
    simp only [Finset.sum_add_distrib,Finset.mul_sum]; congr 1
    · apply Finset.sum_congr rfl; intro k _; dsimp [bornv,field]; rw [hn]; ring
    apply Finset.sum_congr rfl; intro k _; dsimp [bornv,field]; rw [hn]; ring
lemma flip_knob (g h:(Score G Axis QP))(a b:(Branch G Axis))(hp:(parity a ^^ parity b)=true) (l r:Legs (LightMode G QP)): knob g h a b l r=knob g h b a l r:= by
    unfold knob; cases h:parity a <;> cases k:parity b <;> simp_all [Bool.xor] <;> (try exact add_comm ..)
lemma bolt_F (g h:(Score G Axis QP))(l r:Legs (LightMode G QP)): attaches parity (Kzone G) g h l r= ∑ i:ToneS G,( (Spectrum G).fee i:ℂ)* knob g h ((Spectrum G).dual i) ((Spectrum G).plain i) l r:= by
    unfold attaches; simp only [neg_neg,zeroX]; simp_rw [← mul_add];
    change (∑ a:(Branch G Axis),∑ b:(Branch G Axis),Kzone G a b 0*(knob g h a b l r)) = _
    rw [show (∑ a:(Branch G Axis),∑ b:(Branch G Axis),Kzone G a b 0 * knob g h a b l r)= _ from stipend (G:=G) (fun a b=> knob g h a b l r) 0 (fun _=>1) wave]; refine Finset.sum_congr rfl fun i _=> ?_; rw [flip_knob g h _ _ ((Spectrum G).op i)]; push_cast; ring
lemma touching (l:List (LightMode G QP)): run ((Spectrum G).touch F H) l= tree parity (Kzone G) (run F) (run H) l:= by
    change run ((Spectrum G).touch F H) l=A l (attaches parity (Kzone G) (run F) (run H)); simp_rw [Bonded.touching,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,bulb F H _ _ (located _), ← (A l).map_smul, ← map_sum]; congr 1; ext l r; -- lint
    simp_rw [Finset.sum_apply,bolt_F]; rfl
end YM.MS.Tone
