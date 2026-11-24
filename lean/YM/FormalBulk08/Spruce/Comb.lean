import YM.FormalBulk08.Castor.Biscay
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X I:Type}{ρ:ChartRatio G}{Q:Lab G K X}{Θ α:ℝ}{E r e D R:ℕ}{o: Loc G 1}
section
variable (C P P':Pin Q.scrolls)(p:∀ i,C.N i≤ P.N i)(hx:∀ i,P.N i≤ P'.N i)
def PurseT (x:Turn C): Turn P:= ⟨x.toLeaf,x.head.trans_le (p _)⟩
-- zero bad power at cap; monotone with C regardless
lemma bend_up (x: Deck C)(h:0≤Θ): Degree Θ (Lab.raiseD C P p x) ≤ Degree Θ (Lab.raiseD C P p (peak C x.a)) := by
    let S:= (Q.V x.a).S; change ratioR S (P.N x.a) x.b Θ ≤ ratioR S (P.N x.a) (C.N x.a) Θ; unfold ratioR; gcongr
    all_goals first|exact S.strictAnti.antitone x.cap| exact div_nonneg (S.a_pos _).le (S.a_pos _).le|exact S.a_pos _|exact (S.a_pos _).le

def hill (x:X):= Degree targetPower (Lab.raiseD C P p (peak C x))
lemma limb_pos (x:X):0≤hill C P p x:= (ratioR_pos ..).le
include hx
lemma budge (h:Q.Use ρ E)(v:LocalRatio ρ)(a:hue G)(hp:G.Simple): Wells (Dove.tide C) Q.liftF Q.liftU Q.liftH ρ a Q.stub Q.sail (fun i=>hill C P p i.a) (Q.trail P.N) (Q.trail P'.N) (fun x=>instory ρ a Q P.N x.ups) (fun x=> instory ρ a Q P'.N x.ups) E:= by
    let g:= PurseT C P p; obtain W:= Elm.grasp h P P' hx v hp a; have he x:Dove.bump targetPower (g x)≤hill C P p x.a:= bend_up C P p x.ups targetPower_pos.le
    have h1:=flight_bill (W:=Q) h C P.N p; have h2:=flight_bill (W:=Q) h C P'.N (fun x=>(p x).trans (hx x)); have hs: Soft (Dove.tide C) (fun i=>(Dove.tide P).day (g i)):= soft_day (Dove.tide C)
    have hc :Canvas Q.liftF Q.liftU Q.liftH (Dove.tide C) (Q.trail P.N) (Q.trail P'.N) Q.sail (fun i=>hill C P p i.a):= by
       obtain ⟨C',c,u,Q⟩:=W.carts.swirl.lamp; obtain ⟨V,t,w,Y⟩:=W.carts.rays.lamp; refine ⟨⟨h1.swirl,h2.swirl,_, c.reach g,fun i=>u _,fun i=>?_⟩,⟨h1.rays,h2.rays,_, t.reach g,fun i=>w _,fun i=>?_⟩⟩; exacts [strip_mono (Q (g i)) le_rfl (mul_le_mul_of_nonneg_left (he i) (u _)),strip_mono (Y (g i)) le_rfl (mul_le_mul_of_nonneg_left (he i) (w _))]
    exact ⟨Lab.Freight_from h C,hc,fun i=>limb_pos .., W.air.reach g, v,fun x=> W.aV (g x),fun x=>W.bV (g x),fun i ht r=> (Totem_lift (g:=g) hs (W.paid i ht r)).wanes he,fun i=>W.church (g i),fun i hp=> Pact_lift (g:=g) hs (W.weight i hp) he⟩
end
section
variable {A:Page X}{P:Pin A}{θ:ℝ}{g : X→ℝ}{η:Deck P →ℝ}{T: Deck P→ Studio D→Tile (edgeL G) r}
-- multiplier including arbitrary costs
lemma tanne (h:Years A)(hp:θ<α)(hx:θ≤1)(hg:∀ i,0≤g i) (w:Nextpay o (Dove.tide P) (fun i=> η i.ups) (fun i=>η i.bed) (Turn.rad α) (fun i=> g i.a*Dove.bump θ i) r (fun i=> T i.ups) (fun i=>T i.bed))
   (he:Tender ((sage P).reach (peak P)) o (fun i=>η (peak P i)) g (fun i=> T (peak P i))): Tender (sage P) o η (fun i=>g i.a*Degree θ i) T:= by
   obtain ⟨B,b,t,Y⟩:= he; obtain ⟨K,k,c,hK⟩:= w
   let q(x:Turn P):= (((A.mesh x.a).block x.b).val:ℝ); have hu:Soft (Dove.tide P) q:= h.blocks.reach (fun x:Turn P=> x.toLeaf)
   let f(x:Deck P)(b:ℝ):Prop:=∀ p, Knoxville (fame _) (η x) (0,o) (T x p) ((b*(Degree θ x*g x.a))*‖p‖)
   have hv x:f (peak P x) (B x):= by
       have he: Degree θ (peak P x)=1:= by unfold Degree ratioR; rw [show (peak P x).a=x from rfl,show (peak P x).b= P.N x from rfl,div_self ((A.mesh x).a_pos _).ne',Real.one_rpow]
       intro p; rw [he,one_mul,mul_assoc]; exact Y x p
   have ht (x:Turn P)(Z:ℝ)(h:f x.ups Z)(z:0≤Z): f x.bed (Turn.rad (α-θ) x*Z+K x*q x):=by
       let V:=Degree θ x.ups; let U:=Degree θ x.bed;have hp:0<V:=ratioR_pos ..; have he:0<U:=ratioR_pos ..
       have hv:= hK x (Z*(V*g x.a)) (mul_nonneg z (mul_nonneg hp.le (hg _))) h; intro p; apply (hv p).mono; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);change Turn.rad α x*(Z*(V*g x.a))+K x*(g x.a*V) ≤ (Turn.rad _ x*Z+K x*q x)*(U*g x.a)
       have hh:Turn.rad α x*V=Turn.rad (α-θ) x*U:= adjusted _ _ _ _ _
       obtain ⟨M,hM,u,H⟩:= adjust_rate (A.mesh x.a) hx x.b (P.N x.a); have hU : V=M*U:= H; apply le_trans (le_of_eq (b:= (Z*(Turn.rad α x*V)+K x*V)*g x.a) (by ring)); rw [hh,←mul_assoc (Turn.rad (α-θ) x*Z+K x*q x)];apply mul_le_mul_of_nonneg_right _ (hg _); rw [mul_comm Z, mul_right_comm _ U, add_mul]; apply add_le_add_right
       rw [hU]; have hv := c x; calc
                          _ = K x*M*U:= by ring
                          _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u hv) he.le
   obtain ⟨C,c,H,R⟩:= upward h (sub_pos.mpr hp) (f:=f) (fun i A hp B h p=>(hp p).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (mul_nonneg (ratioR_pos ..).le (hg _))) (norm_nonneg _))) b hv (k.times hu) ht
   exact ⟨C,c,H,fun i p=> by dsimp only; rw [mul_comm (g i.a) (Degree θ i),←mul_assoc];exact R i p⟩
end
end YM.FormalBulk08.Spruce
