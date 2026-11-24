import YM.RegulatorIR.Oracle.Frost

/-! Inverse signs exactly from actual Ward tower. Finish motion Sym. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p:Side} {X Y V A B C D:Type} {S T U: Side→ Type}

variable (P:Patch)(K:KernelChoices)(G:Gauge)(B D: Bed)(R: Cross P.L (TypeFace 1) (TypeFace 1))
-- Unique via associative when billed. Need Albedo separate parameters.
lemma medallion [∀ p,Fintype (S p)] {F L:Layer X X} {N:Layer X Y} (W:Quarry X A S)(V:Quarry Y C T)(h:Billed F)(hp:Billed L)(hy:Billed N)(hs:Albedo W W F)(hc:Albedo W W L)(ht:Albedo W V N): lap F (lap L N)=lap (lap F L) N:=by
 apply solely W V (h.lap (hp.lap hy)) ((h.lap hp).lap hy) (hs.lap (hc.lap ht)) ((hs.lap hc).lap ht) (Eventually.of_forall (fun i=> ?_)); intro p; rw [Ledger.lap W W V p h (hp.lap hy) (hc.lap ht),Ledger.lap W W V p (h.lap hp) hy ht,Ledger.lap W W V p hp hy ht,Ledger.lap W W W p h hp hc,Matrix.mul_assoc]
lemma lefte (N:Layer X Y): lap (ID X) N=N :=by ext1 x;ext1 y; unfold lap; rw [tsum_eq_single x,ID,if_pos rfl,one_mul]; intro b hb;rw [ID,if_neg hb.symm,zero_mul]
lemma righte (N:Layer X Y): lap N (ID Y)=N :=by ext1 x;ext1 y;unfold lap; rw [tsum_eq_single y,ID,if_pos rfl,mul_one]; intro b hb;rw [ID,if_neg hb,mul_zero]
variable {G}
lemma Flurry.plus (U H:Layer (Long G.ColorIndex) (Long G.ColorIndex)): Flurry (U+H)=Flurry U+Flurry H:=rfl
lemma Flurry.sub (U H:Layer (Long G.ColorIndex) (Long G.ColorIndex)): Flurry (U-H)=Flurry U-Flurry H:=rfl
lemma Flurry.base (X:Gauge): Flurry (G:=X) (ID _)=ID _:=by funext i j; simp [Flurry,ID]
lemma Flurry.fin {F:Layer (Long G.ColorIndex) (Long G.ColorIndex)}(h:Billed F):Billed (Flurry F):=by obtain ⟨c,hc,h⟩:=h;refine ⟨c,hc,fun i=>(quota_perm (snow G) _ (fun _=>1)).trans_le (h (snow G i))⟩
lemma Flurry.board (A B:Layer (Long G.ColorIndex) (Long G.ColorIndex)): lap (Flurry A) (Flurry B)=Flurry (lap A B):=by ext1 i;ext1 j; exact Eq.symm (Eq.symm ((snow G).tsum_eq (fun z=> A (snow G i) z*B z (snow G j))))
lemma Flurry.power (F:Layer (Long G.ColorIndex) (Long G.ColorIndex))(c:ℝ): Flurry (c • F)=c • Flurry F:=rfl
lemma pension_ice : Flurry (pension P G)=pension P G:=by
 have hv(x: Long G.ColorIndex) : doormat P (snow G x) ↔ doormat P x:=by
    suffices ht:∀ x:Long G.ColorIndex,doormat P (snow G x)→doormat P x by
        exact ⟨ht x, by have he:= ht (snow G x); rw [flinty] at he; exact he⟩ -- direction
    intro x hx h; apply hx; change around _ (reco x.1)∈ _; rw [reco_edge]; exact Geometry.Field.reflect_trunk (F:=stemF P ((1:Side))) (Field.Square.proper _ P.odd_side) h
 ext1 i; ext1 j; simp only [Flurry,pension,hv, (snow G).injective.eq_iff]
variable (G)
local notation "A0"=> projectionQ P K R G
local notation "Q"=> OrthoQ P K G
-- B local param danger
local notation "Kg"=> stableK P K G B
local notation "A"=> blockQ G P.L
local notation "T"=> linksQ G
local notation "L"=> pension P G
variable {σ τ Ω Ω' α α' υ m:ℝ} {S S':Clip}
variable (F:Hall B σ Ω α S)(Xc:Hall D τ Ω' α' S')(Z:P.Branches K G)
variable (H:BidP P K B D R σ υ)(Xs:∀ n,Bid.Sworn B n G)
include F Xs Z
lemma stable_ice : Flurry Kg=Kg :=by
 have hz:=snowed_K G P K Z
 unfold stableK stableL;rw [Flurry.plus,Flurry.power,tune_s G B F Xs,← Flurry.board,hz, show Flurry (Function.swap Q)=Function.swap Q from ?_ ];
 change Function.swap (Flurry Q)=_;rw [hz]
lemma cable_ice : Flurry (cable P K G B F Z)=cable P K G B F Z:=by
 let Q':= cable P K G B F Z; let R':= cousin P K G B;have he : Flurry R'=R':=by
    unfold R' cousin;rw [Flurry.plus, Flurry.sub,← Flurry.board,← Flurry.board,pension_ice,stable_ice P K G B F Z Xs,Flurry.base]
 have hs:= spliceR P K G B; have ha: Billed R':=(shellsC P K G B F).billed F.pos.le (by unfold trunkCost;finiteness)
 have ht:=cafe P K G B F Z; have hh:= (effects P K G B F Z).choose_spec
 have hu: lap R' (Flurry Q')=ID _:=by nth_rw 1 [← he];rw [Flurry.board, show lap R' Q' = _ from hh.2.2.1, Flurry.base]
 have hv : Albedo A A (Flurry Q'):=by
    intro i j d;unfold Flurry; rw [strut,strut,drift_f,drift_f, ← smul_neg,← strut, ← strut]; exact hh.1 ..
 rw [← lefte (Flurry Q'),← show lap Q' R'= _ from hh.2.2.2,← medallion A A ht ha (Flurry.fin ht) hh.1 hs hv]; change lap Q' (lap R' (Flurry Q'))= _;rw [hu,righte]
lemma thaws : Flurry (hearth P K G B F Z)=hearth P K G B F Z:=by unfold hearth; rw [← Flurry.board, ← Flurry.board,cable_ice P K G B F Z Xs,pension_ice]
-- rooted projection uniquely from K. Need $Xc.Accents`. Use arithmetic ledger on all-cover M ties.
include Xc H
omit Xs Z in
lemma aspect : lap (cousin P K G B) A0=lap L (K.penalty • Function.swap Q):=by
 let W':= cousin P K G B
 have hp:=((overrides P K R G H.rows F.pos.le H.costV).buys F.pos.le).1; have hh:=savings P G
 have hb:= pilotK P K G B;have hm:= placates P K R G; have hf:= ((priced_D P K G 0).buys le_rfl).2.smul K.penalty; have hz:= promised P K G
 have hu:Billed W':= (shellsC P K G B F).billed F.pos.le (by unfold trunkCost;finiteness)
 apply solely A T (hu.lap hp) (hh.lap hf) ((spliceR P K G B).lap hm) (hz.lap ((stampD P K G).swap.smul _)) (Eventually.of_forall fun i=>?_)
 intro p; let a:= stableK P K G B; let e:= K.penalty • Function.swap Q
 let M:= ledgerRow A A L p; let Bp:=ledgerRow A T A0 p; let a':= ledgerRow A A a p
 have he:M*Bp=Bp:= by unfold M Bp; rw [← Ledger.lap A A T p hh hp hm, ministry P K G B D R F H]
 have hE:= lifetimeK P K G B F
 rw [Ledger.lap A A T p hu hp hm,Ledger.lap A A T p hh hf ((stampD P K G).swap.smul _)]
 rw [← (marches P K G B D R F Xc H).1,Ledger.lap A A T p hE hp hm]; unfold W' cousin;rw [Ledger.add _ _ _ (hh.lap (hE.lap hh)) (billed_id.sub hh), Ledger.sub _ _ _ billed_id hh, main_zero, Ledger.lap _ A _ p hh (hE.lap hh) (hb.lap hz),Ledger.lap _ A _ p hE hh hz]
 change (M*(a'*M)+(1-M))*Bp= _;rw [Matrix.add_mul,Matrix.mul_assoc M, Matrix.mul_assoc a',he,Matrix.sub_mul,he,Matrix.one_mul,sub_self,add_zero]
end YM.RegulatorIR.Oracle
