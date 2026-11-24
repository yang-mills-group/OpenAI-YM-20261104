import YM.AllOrder.Catch.Mirror
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {ι:Type*} {T:Clock ι} {X Y:ι→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)][∀ i,Fintype (Y i)][∀ i,DecidableEq (Y i)]
variable (V:∀ i:ι,ℝ×(X i × Body (Y i))→ℝ) (W:∀i,X i)
    {A B:∀i,X i× Body (Y i)→ℝ}{M:∀i,X i→ Matrix (Y i) (Y i) ℝ}{ρ:∀ i,X i→Body (Y i)}
-- Morph to EVERY Y filter allowed. require growth Flow for given tableau.N.Incr order exact same Hess (paid.Octane). Need n+3 derivatives on Venue + Lift.Enough requested. Choose Holder proof rewriting.N=H+3. Good.
variable (D u v b p:ι→ℝ) {s z₁:ℝ}{k j:ℕ}
structure Vaccine (k:ℕ)(D u p:ι→ℝ) (T:Clock ι) (A B:∀i,X i× Body (Y i)→ℝ) (ρ:∀ i,X i→Body (Y i)) (M:∀i,X i→ Matrix (Y i) (Y i) ℝ) : Prop where
   D_live : ∀ᶠ i in T.rail, Golf (A i) (B i) (ρ i) (M i) k (D i) (u i) (u i) (p i) ∧ Accent (A i) (B i) (M i) (ρ i)
   price : T.Meter p 0
   rate : Gate T (fun i=> (M i 0)⁻¹) D
   pos : ∀ᶠ i in T.rail,1≤ D i
structure Flood (V:∀ i:ι,ℝ×(X i × Body (Y i))→ℝ)(T:Clock ι)(k:ℕ):Prop where
   rise : ∀ᶠ i in T.rail,Rise (V i)
   ticket : ∀ e, (0:ℝ)<e→∀ᶠ i in T.rail,∀ x:ℝ×(X i× Body (Y i)),‖x‖<1 → Brush k (T.cost i^e) 1 (V i) x
structure North (W:∀ i,X i)(b u:ι→ℝ)(T:Clock ι):Prop where
    W_age : T.Meter (fun i=> ‖W i‖) 0
    early : ∀ᶠ i in T.rail,0<b i ∧ b i*‖W i‖ < u i ∧ b i < u i
    high : T.Meter b (-(1/2))
    low : T.Meter (fun i=> (b i)⁻¹) (1/2)
local notation "Ω" x=> X x × Body (Y x)
local notation "Γ"=> fun i=> grace (A i) (B i) (ρ i) (M i)
variable {W b V D u p} (U:Vaccine k D u p T A B ρ M)(N:North W b u T) (S:Flood V T k)
local notation "F"=> fun i=> course (W i)
local notation "Pt"=> Clock.tier (fun i=>Body (Y i)) T
local notation "Ph"=> T.book (fun i=> closedBall (0:Body (Y i)) (D i))
variable {η:Type*}
namespace Vaccine
include U
lemma reposition (q:η→ι){L:Clock η}(he:T.Fare (U:=L) q): Vaccine (X:=fun i=>X (q i)) (Y:=fun i=>Y (q i)) k (D∘q) (u∘q) (p∘q) L (fun i=> A (q i)) (fun i=> B (q i)) (fun i=>ρ (q i)) (fun i=> M (q i)):= by
 exact ⟨he.tends.eventually U.D_live,U.price.pays q he, Gate.paint_G U.rate q he, he.tends.eventually U.pos⟩
end Vaccine
namespace North
include N
lemma way (q:η→ι){L:Clock η}(he:T.Fare (U:=L) q): North (X:=fun i=> X (q i)) (fun i=> W (q i)) (b ∘ q) (u ∘ q) L:= ⟨N.W_age.pays q he,he.tends.eventually N.early,N.high.pays q he,N.low.pays q he⟩
end North
namespace Flood
include S
lemma paint (q:η→ι){L:Clock η}(he:T.Fare (U:=L) q): Flood (X:=fun i=>X (q i)) (Y:=fun i=>Y (q i)) (fun i=> V (q i)) L k:= by
 refine ⟨he.tends.eventually S.rise,fun e hv=>?_⟩; filter_upwards [he.tends.eventually (S.ticket e hv),he.same] with i hi hV x hX; rw [hV]; exact hi x hX
end Flood
lemma ray (z:∀ i,X i){v:ι→ℝ} (hs:0 ≤ s) (hw:T.Meter v s)(hv:T.Meter (fun i=> ‖z i‖) s) : Cover T k (s+s) (fun _=>1) (fun i=>course (z i)) v:= by
 let L(i:ι):= ContinuousLinearMap.toSpanSingleton ℝ (z i); refine Cover.comp_lin (L:=L) (C:=s) (s:=s) hw.ab hs ?_; simp only [L,ContinuousLinearMap.norm_toSpanSingleton]; exact hv
lemma chum (h:T.Meter p 0)(he:T.Meter D 0)(k:ℕ): T.Meter (fun i=> Lantern.fee k (p i) (D i)) 0 := by
 unfold Lantern.fee; have hx:T.Meter (fun i=>clump k (spanE (p i) (D i)) (p i)) 0:= by
    unfold spanE clump; -- inspect
    let g x:= Meter.const T x
    let gx:=((g 1).add h).add he; exact ((h.lscale _).unitPay le_rfl ((( (g 1).add ((((g 1).add (gx.add gx)).rscale _))).pow _).weak (by simp))) -- shape
 unfold acrossE; let v:= he.unitPay le_rfl (he.unitPay le_rfl hx); exact ((h.add h).add (v.add v)).add (hx.add hx)
lemma chumQ (h:T.Quite p)(he:T.Quite D)(k:ℕ): T.Quite (fun i=> Lantern.fee k (p i) (D i)):= by
 unfold Lantern.fee; have hx:T.Quite (fun i=>clump k (spanE (p i) (D i)) (p i)):= by unfold clump spanE; let g x:= Quite.c T x; let gx:=((g 1).add h).add he; exact (((g _).mul h).mul ((( (g 1).add (((g 1).add (gx.add gx)).mul (g 1)))).pow _)) -- hole
 unfold acrossE; let v:= he.mul (he.mul hx); exact ((h.add h).add (v.add v)).add (hx.add hx)
variable {v}
include N
lemma pole (h:∀ᶠ i in T.rail,|v i|≤ b i): T.Meter v (-(1/2)):= N.high.smaller (h.mono fun i hi=> hi.trans (le_abs_self _))
include U
lemma filming (z:∀ i, Body (Y i)) (h:∀ᶠ i in T.rail,|v i| ≤ b i)(hv:∀ᶠ i in T.rail, ‖z i‖ ≤ D i) : Cover T k 0 (fun _=>1) (fun i t=> Γ i (z i) (t,course (W i) t)) v:= by
 let A' i:= (fun t:ℝ=>(t,F i t)); have he:Cover (V:=fun _=>ℝ) (U:=fun i=>ℝ× X i) T k 0 (fun _=>1) A' v:= Cover.join (Cover.exponent (x:=v) (V:=fun _=>ℝ) le_rfl ((pole N h).weak (by norm_num)|>.ab)) ((ray W ((le_rfl:  (0:ℝ)≤0)) ((pole N h).weak (by norm_num)) N.W_age).weak (by simp));
 refine Cover.weak (Cover.comp (X:=ι) (u:=fun i=> Γ i (z i)) (b:=0) le_rfl he ?_) (by simp); -- p unknown arg
 apply Cover.has (chum U.price U.rate.width k); filter_upwards [hv,U.D_live,N.early,h] with i hi hI hx hz; have hh:‖course (W i) (v i)‖< u i:= by unfold course; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right hz (norm_nonneg _)).trans_lt hx.2.1
 exact Lantern.compel (D i) hI.1 (x:=A' i (v i)) hh (hz.trans_lt hx.2.2) hi
end YM.AllOrder.Catch
