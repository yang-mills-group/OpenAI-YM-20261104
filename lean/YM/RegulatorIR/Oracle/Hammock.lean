import YM.RegulatorIR.Oracle.Bulge
import YM.Next.FREE_KERNELS.Rack

/-! Coverage linear. Comparison stencils missing sym except on full kernel symmetric.
Deduce later with full fold. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {n p:Side} {X Y A V: Type}

variable (P:Patch)(K:KernelChoices)(G:Gauge)(B D: Precision.Bed)(R: Cross P.L (TypeFace 1) (TypeFace 1))
variable {σ τ Ω Ω' α α' υ m:ℝ} {S S':Clip}
variable (F:Hall B σ Ω α S)(C:Hall D τ Ω' α' S')

-- request projection stationarity from Turns Towers.
structure BidP (P:Patch)(K:KernelChoices)(B D:Bed)(R:Cross P.L (TypeFace 1) (TypeFace 1))(σ υ:ℝ):Prop where
 rows : R.strip σ υ
 costV : 0≤υ
 motion (n:Side): Precision.Inputs (avenue P K n) (installed (tileB P.L n) R) (B.metric.acts _) (D.metric.acts _)

variable (H:BidP P K B D R σ υ)
local notation "A0"=> projectionQ P K R G
local notation "Q"=> OrthoQ P K G
local notation "Kg"=> stableK P K G B
local notation "A"=> blockQ G P.L
local notation "T"=> linksQ G
local notation "L"=> pension P G

include F H
lemma ministry : lap L A0=A0:=by
 have hc:= overrides P K R G H.rows F.pos.le H.costV
 have hx:= (hc.buys F.pos.le).1; have hm:= placates P K R G
 apply solely A T ((savings P G).lap hx) hx ((promised P K G).lap hm) hm (Eventually.of_forall (fun i=>?_));intro p
 rw [Ledger.lap A A T _ (savings P G) hx hm, physicalP P K G,projRates P K R G p H.rows F.pos.le H.costV]
 let S:= avenue P K p; let k:= p*P.L;let W:= installed (tileB P.L p) R; let e:= renter P G p;let V:=stemF P p;let K:=FreeResolvent.tensor G (extracted S V W)
 have hv(i:FreeResolvent.Slot G k 1)(j:FreeResolvent.Slot G p 1) (hi:i∉Set.range e): K i j=0:=by
    obtain ⟨v,hv⟩:= show ∃ v,(blockQ G P.L).swrap p v=i from ⟨_,(blockQ G P.L).both _ i⟩
    rw [← hv] at hi ⊢; have hx: around k v.1∈ V.trunks:=by
       by_contra hx; exact hi ((permitsD P G p v).mpr ((admittedE P v).mpr hx))
    unfold K; rw [v_loc]; unfold FreeResolvent.tensor; rw [Matrix.of_apply];split
    next h=> exact (dotProduct_single_one _ (j.1,j.2.1)).symm.trans (Precision.stays V W (Pi.single (j.1,j.2.1) 1) (around k v.1) hx (S:=S))
    rfl
 change FreeResolvent.Shell.rim e*K=K; ext1 x y; rw [Matrix.mul_apply,sum_eq_single x]; rw [FreeResolvent.Shell.indicator];split;exact one_mul _;next he=> rw [hv x y (fun h=> he ⟨rfl,h⟩),mul_zero];
 · intro j hj hd; rw [FreeResolvent.Shell.indicator,if_neg (not_and_of_not_left _ (fun h:x=j=>hd h.symm)),zero_mul] -- check not
 simp
include C
lemma marches:
 lap Kg A0= K.penalty • Function.swap Q ∧ K.penalty • (ID _- lap Q A0)=crust G D:=by
 -- full matrix primal applies K *A = Q.transpose K'. *_WITH inactive RHS? True for all x? yes K A_tr represents Fine Precision full`
 have hs:= stampD P K G; have hb:= placates P K R G;have he:= pilotK P K G B
 have hk:= lifetimeK P K G B F;obtain ⟨hq,hQ⟩:=(priced_D P K G σ).buys F.pos.le; have ha:=((overrides P K R G H.rows F.pos.le H.costV).buys F.pos.le).1
 have hV (n:Side): ledgerRow A T (lap Kg A0) n=ledgerRow A T (K.penalty • Function.swap Q) n ∧ ledgerRow T T (K.penalty • (ID (Long G.ColorIndex)-lap Q A0)) n=ledgerRow T T (crust G D) n:=by
    let s:=avenue P K n; let F':=stemF P n; let W:= installed (tileB P.L n) R
    let Z:= extracted s F' W; let g:=probe s;let M:=K.penalty
    let Tp:= Precision.K (B.metric.acts (n*P.L));let k:= Precision.K (D.metric.acts n)
    have hp:= Precision.stationed (S:=s) F' W (B.metric.acts _) (D.metric.acts _) (H.motion n)
    have hy:g*Z=1 - M⁻¹ • k:= hp.1
    have hf:Tp * Z=g.transpose*k:= hp.2
    rw [Ledger.lap _ (blockQ G P.L) _ n hk ha hb, Ledger.smul,Ledger.rev _ _ n hs,Ledger.smul,Ledger.sub _ _ _ billed_id (hq.lap ha),main_zero,Ledger.lap (linksQ G) (blockQ G P.L) (linksQ G) n hq ha hb,credited P K,physicalK P K G B F,projRates P K R G n H.rows F.pos.le H.costV,crust_id G D C.stripP.2.1 C.pos.le]
    have ht: M≠0:=K.penalty_pos.ne'
    constructor
    · unfold FreeResolvent.fullMatrix; rw [FreeResolvent.tensor_transpose, ← tensor_mul, ← tensor_life] -- fullMatrix def? 
      change FreeResolvent.tensor G ((Tp+M • (g.transpose*g))*Z)=FreeResolvent.tensor G (M • g.transpose); apply congr_arg
      rw [Matrix.add_mul,hf,Matrix.smul_mul,Matrix.mul_assoc g.transpose,hy,Matrix.mul_sub, Matrix.mul_smul,Matrix.mul_one,smul_sub, smul_smul,mul_inv_cancel₀ ht,one_smul,add_sub_cancel]
    rw [← tensor_mul, ← tensor_eye (r:=1) G n,← tensor_sub,← tensor_life] -- names
    change FreeResolvent.tensor G (M • (1-g*Z))= FreeResolvent.tensor G k; rw [hy,sub_sub_cancel,smul_smul,mul_inv_cancel₀ ht,one_smul]
 refine ⟨solely A T (hk.lap ha) (hQ.smul _) (he.lap hb) (hs.swap.smul _) (Eventually.of_forall (fun i=> hV _ |>.1)), solely T T ((billed_id.sub (hq.lap ha)).smul _) (crust_f G D C.stripP.2.1 C.pos.le C.paid) (((Albedo.base T).sub (hs.lap hb)).smul _) (crustA G D) (Eventually.of_forall (fun i=> hV _|>.2))⟩
end YM.RegulatorIR.Oracle
