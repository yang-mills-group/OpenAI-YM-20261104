import YM.RegulatorIR.Oracle.Shells

/-! Committed connections. Pay for the large carriers AFTER this P.
Cover data constructed in the same linearization. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p m: Side} {r s d:ℕ}{L:Side}{η σ:ℝ}
section algebraV
lemma tensor_life {c:ℝ} {A : Matrix (Body r n) (Body s p) ℝ}: FreeResolvent.tensor G (c • A)=c • tensor G A:=by ext i j; unfold FreeResolvent.tensor;simp only [Matrix.of_apply,Matrix.smul_apply];split <;> simp
lemma tensor_eye (G:Gauge)(p:Side): tensor G (1: Matrix (Body r p) (Body r p) ℝ)=1:=by
 ext ⟨i,j,k⟩ ⟨a,b,c⟩; unfold FreeResolvent.tensor; rw [Matrix.of_apply, Matrix.one_apply];split
 next h=> change k=c at h;rw [Matrix.one_apply];simp [h]
 next h=> exact (if_neg (fun q=>(h (congr_arg (fun i : FreeResolvent.Slot G p r=> i.snd.snd) q) : False))).symm
lemma tensor_plus (G:Gauge)(A B:Matrix (Body r n) (Body s p) ℝ): tensor G (A+B)=tensor G A+tensor G B:=by
 ext i j;unfold FreeResolvent.tensor; simp only [Matrix.of_apply,Matrix.add_apply];split <;> simp
lemma tensor_sub (G:Gauge)(A B:Matrix (Body r n) (Body s p) ℝ): tensor G (A-B)=tensor G A-tensor G B:=by ext i j; unfold FreeResolvent.tensor;simp only [Matrix.of_apply,Matrix.sub_apply];split <;> simp
lemma tensor_mul (G:Gauge)(A:Matrix (Body r n) (Body s p) ℝ)(B:Matrix (Body s p) (Body d m) ℝ): tensor G (A*B)=tensor G A*tensor G B:=by
 apply matrixQ;intro v; ext1 i
 rcases i with ⟨i,j,k⟩; change component (G:=G) (tensor G (A*B)*ᵥ v) k (i,j)=component (G:=G) ((tensor G A*tensor G B)*ᵥ v) k (i,j)
 rw [← Matrix.mulVec_mulVec,FreeResolvent.component_mul,FreeResolvent.component_mul,FreeResolvent.component_mul, Matrix.mulVec_mulVec]
end algebraV
-- holds on any $n$. Need purchases.
variable (P:Patch)(K:KernelChoices)(G:Gauge)(B D:Precision.Bed)
abbrev stockA (T:Precision.Towers P.L):= T.A0
def kineticM (B: Precision.Bed) := tensor G (Precision.K (B.metric.acts (n*P.L))) -- n inferred? def body

def stableK: Layer (Long G.ColorIndex) (Long G.ColorIndex):= stableL K.penalty (crust G B) (OrthoQ P K G)
def cousin (P:Patch)(K:KernelChoices)(G: Gauge)(B:Precision.Bed) := lap (pension P G) (lap (stableK P K G B) (pension P G))+ (ID (Long G.ColorIndex)-pension P G)
-- crust working capital uniform $η,C,Grade$ orientation. needed coarsest only for cross and loop estimates.

structure Hall (B:Precision.Bed) (σ Ω α:ℝ)(S:Clip): Prop where
 stripP : B.covered σ Ω
 floorP : ∀ n,Precision.Floor B S n α Ω
 paid : 0 ≤ Ω
 pos :0<σ
 lip :0<α
variable {σ τ Ω φ α α':ℝ} {S S':Clip}
variable (F: Hall B σ Ω α S)
include F
omit F in
lemma pilotK : Albedo (blockQ G P.L) (blockQ G P.L) (stableK P K G B):= (block_inv _ (crustA G B) _).add (((stampD P K G).swap.lap (stampD P K G)).smul K.penalty)
lemma lifetimeK : Billed (stableK P K G B):=by
 obtain ⟨he,h₀⟩:=(priced_D P K G 0).buys le_rfl; exact (crust_f G B F.stripP.2.1 F.pos.le F.paid).add ((h₀.lap he).smul _)
lemma physicalK (n:Side): ledgerRow (blockQ G P.L) (blockQ G P.L) (stableK P K G B) n=FreeResolvent.fullMatrix G (avenue P K n) B.metric:=by
 let S:=avenue P K n; let X:= blockQ G P.L;let Y:=linksQ G
 obtain ⟨he,h₀⟩:=(priced_D P K G 0).buys le_rfl
 have hv:=crust_f G B F.stripP.2.1 F.pos.le F.paid
 unfold stableK stableL; rw [Ledger.add X X n hv ((h₀.lap he).smul _),Ledger.smul,Ledger.lap X Y X n h₀ he (stampD P K G),Ledger.rev _ _ _ (stampD P K G),credited,block_periods _ (crustA G B),crust_id G B F.stripP.2.1 F.pos.le]
 unfold FreeResolvent.fullMatrix FreeResolvent.baseMatrix;rw [tensor_plus,tensor_life,tensor_mul,FreeResolvent.tensor_transpose]
 rfl
omit F in
lemma spliceR : Albedo (blockQ G P.L) (blockQ G P.L) (cousin P K G B):= ((promised P K G).lap ((pilotK P K G B).lap (promised P K G))).add ((Albedo.base _).sub (promised P K G))
lemma touches (n:Side): ledgerRow (blockQ G P.L) (blockQ G P.L) (cousin P K G B) n=FreeResolvent.Shell.pad (renter P G n) (FreeResolvent.fullMatrix G (avenue P K n) B.metric):=by
 let X:=blockQ G P.L; have hp:= savings P G; have he:= lifetimeK P K G B F;have hz:= promised P K G
 rw [cousin,Ledger.add X X n (hp.lap (he.lap hp)) (billed_id.sub hp), Ledger.lap X X X n hp (he.lap hp) ((pilotK P K G B).lap hz),Ledger.lap _ X _ n he hp hz,Ledger.sub X X n billed_id hp,main_zero,physicalK P K G B F,physicalP P K G]; unfold FreeResolvent.Shell.pad FreeResolvent.Shell.off FreeResolvent.Shell.slice; rw [Matrix.mul_assoc]

lemma full_row (n:Side): ledgerRow (blockQ G P.L) (blockQ G P.L) (stableK P K G B) n=ledgerRow (blockQ G P.L) (blockQ G P.L) (lading (blockQ G P.L) (blockQ G P.L) (FreeResolvent.fullRow G P K.penalty B.metric)) n:=by
 rw [physicalK P K G B F, FreeResolvent.fullRow_periods _ F.pos.le F.stripP.2.1,ledger_lade]
 rfl
lemma shapes : chestE (blockQ G P.L) (blockQ G P.L) σ (stableK P K G B) ((Fintype.card (Co P.L (PAC G 1)):ℝ≥0∞)*ENNReal.ofReal (FreeResolvent.outputPrice P K.penalty σ Ω)):=by
 let X:= blockQ G P.L; let R:= FreeResolvent.fullRow G P K.penalty B.metric
 have h: R.strip σ (FreeResolvent.outputPrice P K.penalty σ Ω):=FreeResolvent.fullRow_width P K.penalty F.pos.le F.paid F.stripP.2.1
 have he:= roots X X (M:=R) h
 have ht:stableK P K G B=lading X X R:= solely _ _ (lifetimeK P K G B F) (he.billed F.pos.le (ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top)) (pilotK P K G B) (ladingW _ _ R) (Eventually.of_forall fun _=> full_row P K G B F _)
 rw [ht]; exact he

def trunkCost (G:Gauge)(s c:ℝ):= ((Fintype.card (Co P.L (PAC G 1)):ℝ≥0∞)*ENNReal.ofReal (FreeResolvent.outputPrice P K.penalty s c))+2
lemma shellsC : chestE (blockQ G P.L) (blockQ G P.L) σ (cousin P K G B) (trunkCost P K G σ Ω):=by
 unfold trunkCost;rw [show (2:ℝ≥0∞)=1+1 from by norm_num] -- fix
 have he:= ((pensionE P G).lapB ((shapes P K G B F).lapB (pensionE P G) F.pos.le) F.pos.le).add ((chestE.bright (W:=blockQ G P.L)).sub (pensionE P G)); simp only [mul_one,one_mul] at he; exact he
end YM.RegulatorIR.Oracle
