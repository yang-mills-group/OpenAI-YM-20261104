import YM.RegulatorIR.Momentum.Crest

/-!
# Schur identity with a single insertion drifts TWO histories
Do not pay projectionQ for this repeated step. Includes orientation
signs of ∆ derivatives independent of deck gauge convention.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Layer Budget.Tuple Lattice Laurent Geometry Spatial Sources Oracle Oracle.Quarry RG Bloch Precision Tree PertExtension Geometry.Field Exterior Work.F08 RegulatorIR.Quadratic
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y V:Type} {G:Gauge}{v p:ℕ}{σ τ τ' σ' A A' F F' J S δ ε δ' ε':ℝ}
section algebra
variable [Fintype X][Fintype Y][DecidableEq X][DecidableEq Y] (c:ℝ)(Q:Matrix Y X ℝ)(U Z: Matrix X Y ℝ)(B D:Matrix X X ℝ)(P C:Matrix Y Y ℝ)
omit [DecidableEq X] in
lemma kappa_identity (u:B.transpose=B)(p:P.transpose=P) (h:(B+c • (Q.transpose*Q))*U=c • Q.transpose)(z:(D+c • (Q.transpose*Q))*Z=c • Q.transpose)(hu:P=c • (1-Q*U))(hv:C=c • (1-Q*Z)): P-C=U.transpose*((B-D)*Z):=by
 let A:=c • (Q.transpose*Q)
 have he:A.transpose=A:=by rw [Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_transpose]
 have ht : U.transpose*(B+A)=c • Q:=by rw [← u,← he,← Matrix.transpose_add, ← Matrix.transpose_mul,h,Matrix.transpose_smul,Matrix.transpose_transpose]
 rw [show B-D=B+A-(D+A) by abel, Matrix.sub_mul,z,Matrix.mul_sub,← Matrix.mul_assoc U.transpose,ht,Matrix.smul_mul,Matrix.mul_smul]
 have hP:P=c • (1-U.transpose*Q.transpose):=by nth_rw 1 [← p]; rw [hu,Matrix.transpose_smul,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_one]
 rw [hP,hv,smul_sub,smul_sub];abel
end algebra

variable (G:Gauge) (K:KernelChoices)(P:Patch)
variable {B C D E:Precision.Bed}
variable (R R' : Cross P.L (TypeFace 1) (TypeFace 1))
variable {s l t q:RG.Clip}
variable (H:Hall B σ F δ s)(Ω: Hall C τ A ε l)(Z: Hall D σ' F' δ' t)(H': Hall E τ' A' ε' q)
variable (S₁: BidP P K B C R σ J)(S₂:BidP P K D E R' σ' S)
local notation "Xb"=>blockQ G P.L
local notation "W"=>linksQ G
local notation "q₀"=> OrthoQ P K G
local notation "e"=> projectionQ P K R G
local notation "e'"=>projectionQ P K R' G
local notation "P₀"=> crust G B
local notation "P₁"=> crust G C
local notation "P'"=> crust G D
local notation "P''"=>crust G E

lemma comm_lane (B:Bed){α σ Ω:ℝ} {C:Clip}(Xv:Hall B σ Ω α C) (T:Cross P.L (TypeFace 1) (TypeFace 1)) {H D:ℝ}(hp:T.strip H D)(h₀:0≤ D)(ht:0≤H):
 lap (crust G B) (projectionQ P K T G)=lap (crust G B) (ruling P G T):=by
 have hz:=(overrides P K T G hp ht h₀).buys ht|>.1
 have h:= crust_f G B Xv.stripP.2.1 Xv.pos.le Xv.paid
 have hv:= ((fond Xb W _ (adult_price G P T hp h₀)).buys ht).1
 change Billed (ruling P G T) at hv
 let z:=block_inv (crust G B) (crustA G B) P.L
 apply solely Xb W (h.lap hz) (h.lap hv) (z.lap (placates P K T G)) (z.lap (albedoX P T G)) (Eventually.of_forall fun i=>?_)
 intro p; rw [Ledger.lap Xb Xb W _ h hz (placates P K T G),Ledger.lap Xb Xb W _ h hv (albedoX P T G), block_periods (crust G B) (crustA G B), crust_id G B Xv.stripP.2.1 Xv.pos.le, projRates P K T G p hp ht h₀, seatV, ← tensor_mul, ← tensor_mul]
 apply congr_arg; rw [Precision.extracted, Matrix.mul_add]
 have he : (Precision.K (B.metric.acts (p*P.L)))*Exterior.d 0 (p*P.L)=0:=by rw [Precision.K,Matrix.mul_assoc,Exterior.closed,Matrix.mul_zero];
 rw [← Matrix.mul_assoc,he,Matrix.zero_mul, add_zero]
include H H' Z Ω S₁ S₂
lemma upwards : P₁-P''=lap (Function.swap e) (lap (P₀-P') e'):=by
 have h:= crust_f G B H.stripP.2.1 H.pos.le H.paid
 have h':= crust_f G D Z.stripP.2.1 Z.pos.le Z.paid
 have he:= (overrides P K R G S₁.rows H.pos.le S₁.costV).buys H.pos.le
 have he':= (overrides P K R' G S₂.rows Z.pos.le S₂.costV).buys Z.pos.le
 have hv₁:=placates P K R G;have hv₂:=placates P K R' G
 have hm:= (priced_D P K (G:=G) (0:ℝ)).buys le_rfl
 apply solely W W ((crust_f G C Ω.stripP.2.1 Ω.pos.le Ω.paid).sub (crust_f G E H'.stripP.2.1 H'.pos.le H'.paid)) (he.2.lap ((h.sub h').lap he'.1)) ((crustA G C).sub (crustA G E)) (hv₁.swap.lap (((block_inv P₀ (crustA G B) _).sub (block_inv P' (crustA G D) _)).lap hv₂)) (Eventually.of_forall fun i=>?_)
 intro n
 let U:= ledgerRow Xb W e n;let T:= ledgerRow Xb W e' n
 let Q:= ledgerRow W Xb q₀ n
 rw [Ledger.sub W W n (crust_f G C Ω.stripP.2.1 Ω.pos.le Ω.paid) (crust_f G E H'.stripP.2.1 H'.pos.le H'.paid),Ledger.lap W Xb W n he.2 ((h.sub h').lap he'.1) (((block_inv P₀ (crustA G B) _).sub (block_inv P' (crustA G D) _)).lap hv₂),Ledger.lap Xb Xb W n (h.sub h') he'.1 hv₂,Ledger.sub Xb Xb n h h',Ledger.rev _ _ n hv₁]
 have z:= stampD P K G
 obtain ⟨hU,hP⟩:= marches P K G _ _ _ H Ω S₁
 obtain ⟨hx,hz⟩:=marches P K G _ _ _ Z H' S₂
 refine kappa_identity K.penalty Q U T _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
 · rw [← Ledger.rev _ _ n (block_inv P₀ (crustA G B) _),symmetry_h G B H.floorP H.pos.le H.paid H.stripP.2.1]
 · rw [← Ledger.rev _ _ n (crustA G C),symmetry_h G C Ω.floorP Ω.pos.le Ω.paid Ω.stripP.2.1]
 · have hv:= congr_arg (fun L=> ledgerRow Xb W L n) hU
   rw [Ledger.lap _ Xb _ n (lifetimeK P K G B H) he.1 hv₁,stableK, stableL, Ledger.add Xb Xb n h ((hm.2.lap hm.1).smul _), Ledger.smul,Ledger.lap Xb W Xb n hm.2 hm.1 z, Ledger.smul,Ledger.rev _ _ n z] at hv;exact hv
 · have hv:= congr_arg (fun L=> ledgerRow Xb W L n) hx
   rw [Ledger.lap _ Xb _ n (lifetimeK P K G D Z) he'.1 hv₂,stableK, stableL, Ledger.add Xb Xb n h' ((hm.2.lap hm.1).smul _), Ledger.smul,Ledger.lap Xb W Xb n hm.2 hm.1 z, Ledger.smul,Ledger.rev _ _ n z] at hv;exact hv
 · have hv:= congr_arg (fun L=>ledgerRow W W L n) hP; rw [Ledger.smul,Ledger.sub W W n billed_id (hm.1.lap he.1),Ledger.lap W Xb W n hm.1 he.1 hv₁, main_zero] at hv;exact hv.symm
 have hv:= congr_arg (fun L=>ledgerRow W W L n) hz; rw [Ledger.smul,Ledger.sub W W n billed_id (hm.1.lap he'.1),Ledger.lap W Xb W n hm.1 he'.1 hv₂, main_zero] at hv;exact hv.symm
end YM.RegulatorIR.Momentum
