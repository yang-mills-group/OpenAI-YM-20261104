import YM.MS.ChargeValue
import YM.MS.Color.Components
import YM.MS.Properties

set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect
open Function Filter Set Finset Plane Koszul Real Momentum
open scoped Topology ContDiff InnerProductSpace
variable {G: Gauge}
abbrev FourP:= Momentum Axis
abbrev Law (G : Gauge):= Score G Axis FourP
abbrev natQ := (send (C:= G.ColorIndex) (id:FourP→FourP)).raise
variable {F: Law G}
abbrev qnote (i:Atom Axis) (c:CI G) (p : FourP) : Lane4 G:= ((i,c),p)
abbrev W (i:Axis) (c:CI G):= qnote (gauge i) c
abbrev C (c:CI G):= qnote ghost c
abbrev U (i:Axis) (c:CI G):= qnote (anti i) c
abbrev S (c:CI G):= qnote gaugeC c
section flux
open Complex (I)
lemma qAA (F : Law G) (a : Axis) (p: FourP) (i : CI G) w: natQ F (W a i p::w) = (∑ j:Axis, -(precision j a p:ℂ)* F (U j i p::w)) + natQ (Koszul.D (W a i p) F) w := by
   rw [natQ,Charge.act_at]; simp [send,choir,parity,Landau.p,bare,Fintype.sum_prod_type,Fintype.sum_option,qnote,U,W,ite_mul]
lemma qGhost (F : Law G) (p: FourP) (i : CI G) w: natQ F (C i p::w) = (∑ j:Axis, I*(p j:ℂ)* F (W j i p::w)) - natQ (Koszul.D (C i p) F) w := by
   rw [natQ,Charge.act_at]; simp [send,choir,parity,Landau.p,bare,Fintype.sum_prod_type,Fintype.sum_option,qnote,C,ghost,W,ite_mul,sub_eq_add_neg]
lemma qAnti (F : Law G) (a : Axis) (p: FourP) (i : CI G) w: natQ F (U a i p::w) = -(I*(p a:ℂ))* F (S i p::w) - natQ (Koszul.D (U a i p) F) w := by
   rw [natQ,Charge.act_at]; simp [send,choir,parity,Landau.p,bare,Fintype.sum_prod_type,Fintype.sum_option,qnote,U,S,ite_mul,sub_eq_add_neg]
lemma qS (F : Law G) (p: FourP) (i : CI G) w: natQ F (S i p::w) = natQ (Koszul.D (S i p) F) w:= by
   rw [natQ,Charge.act_at]; simp [send,choir,parity,Landau.p,bare,qnote,S]
@[simp] lemma q0 (F : Law G) : natQ F []=0:= by simp [natQ, Charge.raise]
end flux
end YM.MS.Landau.Detect
