import YM.FormalBulk08.Spruce.Fair
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K: KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H:Hol G}
variable {ρ:ChartRatio G}{o:Loc G 1}{Y Z:X→Anthem D G}{g:X→ℝ}{θ:ℝ}{τ:Time X}
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P Q:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hz:∀ i,P.N i≤ Q.N i)(hl:l ≤ R)(hR:d≤ R)
    (hg:∀ i,0≤ g i) (hy:∀ i,Clef o (Y i) l)(hx:∀ i,Clef o (Z i) l)
    (hw:∀ e≤ E,∀ r,Brass ((sage C).reach (peak C)) o (fun i=> W.eagle (peak C i)) (hill C P hp) g (fun x p=> Y x p e r) (fun x p=> Z x p e r))
structure Erudit (τ:Time X)(P:Page X)(C:Pin P): Prop where
    origin:Soft τ (fun x=> (sage C).day (startP x C))
    depth: Soft τ (fun x=>sowing (P.mesh x) (P.ell x) (C.N x))
variable (Hq:Erudit τ _ C)(he:θ<1/2)(Ht:0≤θ)
include q u h a hs ht hb hz hp hR Hq
lemma tunes (x y:Letter F): Priced (qday τ C) (fun i=>hill C P hp i.a) (fun i=>(echoR T ρ q a C P i)⁻¹ x y) (fun i=>(echoR T ρ q a C Q i)⁻¹ x y) E:= by
    let g(i:Turn C): transferPoint W:= ⟨i.toLeaf,P.N i.a,Q.N i.a,i.head.trans_le (hp i.a),hz _⟩; have hv i: spinR targetPower (g i) ≤ hill C P hp i.a:= bend_up C P hp i.ups targetPower_pos.le
    have hp:= (tabular Hq.origin Hq.depth u.liable).reach (fun i:Turn C=> i.bed); exact fun j hj=> Pact_lift (g:=g) hp (runwayBack q u h a hs ht hb hR x y _ hj) hv
include hx hy hw hl hg he Ht
lemma aboard (x:Letter F)(hv:e≤ E) : Calm (rday τ C) (fun i=>hill C P hp i.a) (fun i=>g i.a*Degree θ i) (fun i=> coeff e (debt l T ρ q a C P Y i x ())) (fun i=> coeff e (debt l T ρ q a C Q Z i x ())) := by
    obtain hA:=tabular Hq.origin Hq.depth u.liable
    let δ:=hill C P hp; have hh:= hA.reach (fun i:Turn C=> i.bed); have ht'(i:Turn C):= (mat_begins a h q hs ht hb i.a i.b (P.N i.a) i.zone (i.head.trans_le (hp _))).1; have hv' (i:Turn C):=(mat_begins a h q hs ht hb i.a i.b (Q.N i.a) i.zone (i.head.trans_le ((hp _).trans (hz _)))).1
    have h1:(∀ i:Turn C, Fresh (wrist ρ a W P i.a i.b)):= by intro i; exact (Lab.pesto h a hs (i:= (⟨i.toLeaf,P.N i.a,Q.N i.a,i.head.trans_le (hp _),hz _⟩:transferPoint W)) _ (i.head.trans_le (hp _))).1
    have h2:(∀ i:Turn C, Fresh (wrist ρ a W Q i.a i.b)):= by intro i; exact (Lab.pesto h a hs (i:= (⟨i.toLeaf,P.N i.a,Q.N i.a,i.head.trans_le (hp _),hz _⟩:transferPoint W)) _ (i.head.trans_le ((hp _).trans (hz _)))).1
    let s (z):=nextU (wrist ρ a W P (z:Turn C).a z.b); let t z:=nextU (wrist ρ a W Q (z:Turn C).a z.b);
    have hx1:= budge C P Q hp hz u h a hs; have hQ: Priced (qday τ C) (fun i=>δ i.a) s t E:= fun j hj=> Pact_lift (g:=id) hh (hx1.weight.next h1 h2 j hj) (fun _=>le_refl _)
    let b:=fun (x:Deck C)=>g x.a*Degree θ x
    let G (x:Turn C)(i:Letter F):ℝ:= (heightK ((W.V x.a).S.block x.b) d (Pose.weight F i))⁻¹
    let A (i:Turn C):= (echoR T ρ q a C P i)⁻¹; let B (i:Turn C):= (echoR T ρ q a C Q i)⁻¹
    let D' i:= debt l T ρ q a C P Y i; let T' i:=debt l T ρ q a C Q Z i; let f i:= feed (T:=T) l ρ q a C P i Y; let F' i:=feed (T:=T) l ρ q a C Q i Z
    have hD(i:Turn C): D' i.ups=(A i*(f i+D' i.bed)).map (PowerSeries.subst (PowerSeries.X*s i)) := fee l T ρ q a C P Y i
    have hE(i:Turn C): T' i.ups=(B i*(F' i+T' i.bed)).map (PowerSeries.subst (PowerSeries.X*t i)) := fee l T ρ q a C Q Z i
    have hU (i k): Priced (qday τ C) (fun i=>δ i.a) (fun x=>A x i k) (fun x=>B x i k) E:= tunes q u h a hs ht hb C P Q hp hz hR Hq i k
    have hF (i)(k:Unit)(e)(hp':e≤E): Calm (qday τ C) (fun i=>δ i.a) (fun i=>b i.ups) (fun p=>coeff e (f p i k)) (fun p=>coeff e (F' p i k)):=by
        have hh' := uses_fee q u h a hs ht hb C P Q hp hz hl hR hg hy hx hw he (by linarith) i hp'; cases k; have hz:= Calm.lifted (τ:=Dove.tide C) id (qday τ C) hh hh'; exact hz
    have hp' i:Found (Pose.slots F) (Pose.weight F) (A i) (G i):= down (ht' i).back; have hx' i:Found (Pose.slots F) (Pose.weight F) (B i) (G i):=down (hv' i).back
    have hv i:D' (startP i C)=0:= bills_empty l T ρ q a C P Y i (W.neck i) le_rfl; have hw i:T' (startP i C)=0:= bills_empty l T ρ q a C Q Z i (W.neck i) le_rfl
    exact momentum (S:=D') (Q:=T') (f:=b) (τ:=τ) (δ:=δ) (P:=C) hp' hx' (fun i j=>inv_le_one_of_one_le₀ (crown_weight _ j)) hv hw hD hE (fun i=> fresh_N _) (fun i=>fresh_N _) (raySteps Hq.depth) (fun i=>limb_pos ..) (fun i=>mul_nonneg (hg _) (ratioR_pos ..).le) (fun i=>mul_le_mul_of_nonneg_left (deg_out _ C Ht i) (hg i.a)) hU hQ hF x () e ‹e≤ E›
end YM.FormalBulk08.Spruce
