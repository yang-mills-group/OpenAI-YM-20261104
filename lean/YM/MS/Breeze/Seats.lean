import YM.MS.Breeze.Wine
import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.State
/-! Price at each scale for gluing/Wick.S.Submodule -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Breeze
open Garment.Wick
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Puff Rake Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{F H:Law G}{t:ℝ}
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
local notation "K"=> (Job.single Unit)
local infix:70 " ⋄ "=> product (field Landau.parity)
-- copy Fleet and adapt. Continuum offset.Code.cumulative
variable {s n:ℝ} {P:Latch.Edge G}(a b:QP)
def chair (G:Gauge)(a:QP): Op (Lane4 G) ℂ:= {
   toFun f w:= Tone.bill a ( net w )* f w
   map_add' _ _:= funext fun _=> mul_add ..
   map_smul' _ _:= funext fun _=> mul_left_comm .. }
lemma seated (F:Law G)(w:Legs (Lane4 G)): chair G a F w= Tone.bill a ( net w ) * F w:= rfl
lemma faith_m : chair G 0 F=F := by ext; simp_rw [seated,pay0,one_mul ]
lemma climb : chair G a ( chair G b F ) = chair G ( a+b ) F:= by ext; simp_rw [ seated, Tone.payadd,mul_assoc ]
lemma chair_product : (chair G a ( F ⋄ H )) = chair G a F ⋄ chair G a H:= by
    funext l; rw [seated]; simp_rw [ scattered ]; let Q:= allocate Ψ l (R:=ℂ); change ( Tone.bill a ( net l ) ) • Q _=Q _; rw [← map_smul]; refine scatter_congr _ _ _ _ (fun x y he=>?_); simp_rw [ seated,← split_net he,Tone.rightadd,Pi.smul_apply,smul_eq_mul ]; ring
lemma chairDeep (F:Law G)(s:ℝ): Ccy (PlanetD G s) ( chair G a F ) planeF=chair G a ( Ccy (PlanetD G s) F planeF ):= by funext l; unfold Ccy; rw [seated,← integral_const_mul ]; simp_rw [ at_trc,seated,net_cons, ← add_assoc, add_neg_cancel,zero_add,mul_left_comm ( PlanetD G s _ _ _ ) (Tone.bill _ _),← Finset.mul_sum ]
lemma chair_free : (chair G a (coin (1:ℂ)))=coin 1:= by ext l; cases l with| nil=> rw [seated]; simp [net] | cons i l=> rw [seated]; exact mul_zero _ -- mul zero
lemma chair_t (f:Local.BV.Grade G): chair G a (mono f) = mono (fun x=> bill a x.2*f x):= by funext v; rcases v with _|⟨i,_|x⟩; exact mul_zero _; change Tone.bill a ( net [i] )*f i=_; simp [net]; rfl; exact mul_zero _
lemma chair_v (h:F∈ Wallet G): chair G a F∈ Wallet G:= by
    apply permits.mpr; intro E _ _ W; unfold fieldVal; simp_rw [ seated,sail_net ]; exact pulse_bill (V:=fun (_:Unit)=>a) ( net W ) ( permits.mp h E W ) ⟨‖a‖+1,by positivity,0, fun i p _=> by simp [ Job.single ]⟩
lemma chair_p (hp:F∈Roof G): chair G a F∈ Roof G:= ⟨ chair_v a hp.1,fun l hl=> by rw [seated, hp.2 l hl, mul_zero ] ⟩
lemma chair_move (hp:F∈Wallet G)(s:ℝ): deep G s (chair G a F)=chair G a (deep G s F):= by rw [ weightC hp, weightC ( chair_v a hp ), chairDeep ]
lemma netπ (p:QP): Tone.bill (a-b) p=Tone.bill a p * ( Tone.bill b p )⁻¹:= by rw [ sub_eq_add_neg,Tone.payadd,Tone.opp ]
private lemma net_C (i j:BH G)(x y:Legs (Lane4 G))(p:QP): meshZ P i j ( chair G a F ) ( chair G b H ) x y p= Tone.bill a ( net x )*Tone.bill b ( net y )*(Tone.bill ( a-b ) p*meshZ P i j F H x y p):= by
    simp only [meshZ,seated,net_cons,Tone.rightadd,Tone.inverse,netπ]; ring
lemma climb_c (hF:F∈ Wallet G)(ht:H∈ Wallet G)(s:ℝ): linkD G s ( chair G a F ) ( chair G b H ) = chair G b (Cabin ( a-b ) ( PlanetD G s ) planeF F H):= by
    rw [ oriented ( chair_v a hF ) ( chair_v b ht ) ]; funext w; unfold Cabin; rw [seated]; let Q:= allocate Ψ w ( R:=ℂ ); change Q _= Tone.bill b (net w) • Q _; rw [← map_smul]; apply scatter_congr; intro x y he; simp_rw [Tone.pay0,one_mul,net_C,integral_const_mul, ← Finset.mul_sum ]; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul,← split_net he,Tone.rightadd, netπ ]; field_simp [ nonz ] -- Ipc dims cost.P.
end YM.MS.Breeze
