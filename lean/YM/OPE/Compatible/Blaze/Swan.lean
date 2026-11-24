import YM.OPE.Compatible.Blaze.Will
/-! # Quadratic score interchange -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Coin
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {N c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis) (S:StepData c f) (h:Odd S.ratio.count.val)
local notation "Fr"=> forest S.ratio h
local notation "X"=> Bid.Dir G c
local notation "Y"=> AxisChart G (forest S.ratio h)
variable {K:Sponsor G}{T:Seasons K}{i:ℕ}{v u r':ℝ}{A:Alps K T i v}{b:ℝ}
variable (U:Boxes G S.patch S.kernel) (t:S.Choices){Z:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio h)} (L':FibreRep S h U t A g b)(H:licensed S h U A.clip A.live Z A.sky g)
attribute [local instance] Gauge.frobInner
include H L'
open Radial
local notation "Ω"=> Zig a S h (G:=G)
local notation "Ψ"=> plank a S.ratio h (G:=G)
include a
open Adhesion
lemma P_buffer (v:Y): L'.L.Q.P v v=L'.L.Q.P (Ψ v) (Ψ v):=by
     have ht(v:Y): jet L'.L.f 2 (0,v)=jet L'.L.f 2 (0,0)+L'.L.Q.P v v/2:=by simpa only [map_zero,zero_add] using L'.L.split 0 v
     have hh:= lamp_coin a S h U t L' H (0,v) 2 (by decide); rw [show Ω (0,v)=(0,Ψ v) from Prod.ext (map_zero (streak a G c)) rfl, ht,ht v] at hh; linarith
omit H a in
lemma definite (y:Y)(x:X): jet L'.L.f 2 (x,L'.L.M x)≤ jet L'.L.f 2 (x,y) ∧ (jet L'.L.f 2 (x,L'.L.M x)=jet L'.L.f 2 (x,y)→ y=L'.L.M x):=by
    let z:=y-L'.L.M x; have hp:=L'.L.split x z; obtain ⟨c,hc,ht⟩:=L'.L.Q.slope; have ht:=ht z; rw [show L'.L.M x+z=y from add_sub_cancel ..] at hp; rw [hp]; constructor; exact le_add_of_nonneg_right (le_trans (by positivity) ht)
    intro h; apply sub_eq_zero.mp; by_contra hs; have hz:0<L'.L.Q.P z z/2:=lt_of_lt_of_le (mul_pos hc (pow_pos (norm_pos_iff.mpr hs) _)) ht; linarith
lemma wingCash (x:X): L'.L.M (streak a G _ x)=Ψ (L'.L.M x):=by
    let T:= L'.L.M; let Z:=jet L'.L.f 2; let u: X:=streak a _ _ x; have hp(y:Y):Z (x,Ψ y)= Z (u,y):=by rw [show Z _= _ from (show Z (x,Ψ y)= Z (Ω (x,Ψ y)) from (lamp_coin a S h U t L' H _ 2 (by decide)).symm),show Ω (x,Ψ y)=(u,y) from Prod.ext rfl (bloom2 a S.ratio h y)]
    have ht:= (definite S h U t L' (Ψ (T x)) u); symm; apply ht.2; apply le_antisymm ht.1; change Z (u,Ψ (T x)) ≤ Z (u,T u); rw [← (show Z (x,Ψ (Ψ _)) = Z (u,Ψ (T x)) from hp _),← show Z (x,Ψ (T u))=Z (u,T u) from hp _,bloom2]; apply (definite S h U t L' _ _).1
lemma bark (x:X×Y): Ω (Fiber.drape X Y L'.L.M x)= Fiber.drape X Y L'.L.M (Ω x):=by apply Prod.ext; rfl; change Ψ (L'.L.M x.1+x.2)= L'.L.M (streak a G c x.1)+_; rw [map_add,show L'.L.M _= _ from wingCash a S h U t L' H x.1];rfl
lemma keepFee (x:X×Y)(p:LocalRatio P):L'.L.cloth P (Ω x)= L'.L.cloth P x:=by
    unfold Fiber.cloth; rw [Function.comp_apply,← bark a S h U t L' H,Function.comp_apply]; let f:=L'.L.f; let w:=L'.L.wSign P; let y:=Fiber.drape X Y L'.L.M x; change Adhesion.Curling f w (Ω y) =Adhesion.Curling f w y; have he(j:ℕ):jet w j (Ω y)=jet w j y:=by
         unfold jet; conv_rhs=> rw [← ((toll_v a S h U t L' H p).iteratedFDeriv ℝ j).eq_of_nhds, jets_linear _ ((L'.L.signB p).of_le (WithTop.coe_le_coe.mpr le_top))]; rfl -- heartbeat
         rfl
    unfold Adhesion.Curling Adhesion.GateT; rw [Pi.mul_apply, Pi.mul_apply]; apply congr_arg; apply congr_arg₂ (·*·); exact JetS.eta _ _ (he _) (he _) (he _)
    have hv:=lamp_coin a S h U t L' H y; apply JetS.eta
    · rfl
    · exact congr_arg Neg.neg (hv 3 (by decide))
    change -jet L'.L.f 4 (Ω y)+_ =_; rw [hv 4 (by decide)]; change _+(jet _ 3 (Ω y))^ _ /_= _; rw [show jet _ 3 (Ω y)=_ from hv 3 (by decide)]; rfl
local notation "µ"=>Chart.tangent G (Forest.Free (forest S.ratio h))
lemma DualSum (x:Y→Token)(p:ScriptJ.B x): Libra.draw x L'.L.Q µ= Libra.draw (x ∘ Ψ) L'.L.Q µ:=by
     let Z :Y≃ₗ[ℝ] Y:={ (plank a S.ratio h (G:=G)).toLinearMap with invFun:=Ψ,left_inv:=bloom2 a S.ratio h,right_inv:=bloom2 a S.ratio h}
     have he(i):Bond (fun t=>(x t).seq i):=p i
     have hv(i):= meanFit µ µ L'.L.Q L'.L.Q Z.toLinearMap (dual_wick Z _ _ (P_buffer a S h U t L' H)) _ (he i)
     exact JetS.eta _ _ (hv 0) (hv 1) (hv 2)
lemma PrizeTurn (p:LocalRatio P)(y:X×Y→Token)(hp:ScriptJ.B y)(x:X):L'.L.predicts P y (streak a G c x) = L'.L.predicts P (y∘ Ω) x:=by
     let S':= L'.L.cloth P; let L:= Fiber.drape X Y L'.L.M; let u:=streak a G c x; unfold Fiber.predicts; let q: X×Y → Token:= (y∘ L)* S'; have hv:ScriptJ.B S':=L'.L.cloth_B p; have he:ScriptJ.B q:= ScriptJ.height (p:=y∘ L) (fun i=> (hp i).compLinear L.toLinearMap) hv; change Libra.draw (fun t=>q (u,t)) L'.L.Q µ/ Libra.draw (fun t=> S' (u,t)) _ _= _; rw [DualSum a S h U t L' H (fun v=>q (u,v)) _, DualSum a S h U t L' H (fun v=>S' (u,v)) _]; rotate_left 1
     · intro i; exact Shift.leanB _ (hv i) u -- name
     · intro i; exact Shift.leanB _ (he i) u
     have hh(v:Y): Ω (x,v)=(u,Ψ v):=rfl
     apply congr_arg₂ (·/·)
     · change Libra.draw _ _ _= Libra.draw _ _ _; congr 1; funext i; rw [Function.comp_apply]; change y (L _)*S' _=_; change y (L (u,Ψ i))* S' (u,Ψ i)= _; rw [←hh,← bark a S h U t L' H (x,i), show S' _=_ from keepFee a S h U t L' H _ p]; rfl
     change Libra.draw _ _ _=Libra.draw _ _ _; congr 1; funext i; rw [Function.comp_apply]; exact keepFee a S h U t L' H (x,i) p
end YM.OPE.Quit
