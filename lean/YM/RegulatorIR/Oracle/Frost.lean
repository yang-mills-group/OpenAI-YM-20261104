import YM.RegulatorIR.Oracle.Hammock
import YM.Extra.ITERATION_NO_LOSS.Channel

/-! Gate orientation. T signs on site vs potential legs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open Extra.Iteration.Channel
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge} {n p:Side} {X Y A B:Type}

def snow (G:Gauge): Equiv.Perm (Long G.ColorIndex):= Equiv.prodCongr (Equiv.mk Geometry.reco Geometry.reco reco_twice reco_twice) (Equiv.refl _)
lemma drift_f (x:Long G.ColorIndex)(u:Cover) : snow G (motionsQ x u)= motionsQ (snow G x) (-u):=Prod.ext (dis_reco u x.1) rfl
lemma flinty (G:Gauge)(i): snow G (snow G i)=i:= (snow G).left_inv _

def Flurry (L:Layer (Long G.ColorIndex) (Long G.ColorIndex)):Layer (Long G.ColorIndex) (Long G.ColorIndex):= fun i j=> L (snow G i) (snow G j)
def iceE (G:Gauge)(n): Equiv.Perm (FreeResolvent.Slot G n 1):= let X:= Equiv.prodCongr (Equiv.mk Orb.reflect Orb.reflect Orb.reflect_reflect Orb.reflect_reflect) (Equiv.refl G.ColorIndex); (onslot G n).symm.trans (X.trans (onslot G n))
lemma snow_ice (G:Gauge)(n) i: iceE G n ((linksQ G).swrap n i)= (linksQ G).swrap n (snow G i):=by
 rw [← on_wrap,← on_wrap]; unfold iceE; rw [Equiv.trans_apply,(onslot G n).symm_apply_apply]; refine congr_arg (onslot G n) (Prod.ext ?_ rfl); exact (reco_edge i.1).symm
lemma snow_c (G:Gauge)(n L) i: iceE G (n*L) ((blockQ G L).swrap n i)= (blockQ G L).swrap n (snow G i):=by rw [v_same, v_same,snow_ice]
lemma ice_i (G:Gauge)(n) (i) : iceE G n (iceE G n i)=i:=by
 obtain ⟨x,rfl⟩:= (show Surjective ((linksQ G).swrap n) from fun i=>⟨_, (linksQ G).both ..⟩) i;rw [snow_ice,snow_ice,flinty]
lemma frosting {P S:Side→Type}(D:Quarry (Long G.ColorIndex) X P)(F:Quarry (Long G.ColorIndex) A S)(M:Layer (Long G.ColorIndex) (Long G.ColorIndex)) (h:Billed M)(hp:∀ n:Side,∀ i j,
 ledgerRow D F M n (D.swrap n i) (F.swrap n j)= ledgerRow D F M n (D.swrap n (snow G i)) (F.swrap n (snow G j)))(he:Albedo D F M):Flurry M=M:=by
 funext i j; exact tendsto_nhds_unique ((ledger_limit D F h he (snow G i) (snow G j)).congr (fun x=> (hp _ i j).symm)) (ledger_limit D F h he i j)

variable (G n)

def snowU (x:FreeResolvent.Vec G n 1): FreeResolvent.Vec G n 1:= fun i=>-x (iceE G n i)
lemma where_about (x: Bid.Dir G n):FreeResolvent.flatten (Bid.pulled x invS)=snowU G n (FreeResolvent.flatten x):=by
 ext1 i; obtain ⟨v,rfl⟩:= (show Surjective ((linksQ G).swrap n) from fun x=> ⟨_,(linksQ G).both ..⟩) i
 unfold snowU;rw [snow_ice,← on_wrap,← on_wrap]
 let z:= around n v.1
 change (Bid.pulled x invS (bondBody n z)) v.2 = _; rw [pulled_edge];
 have ht: sendEdge invS (0:Site n) z= Orb.reflect z:=by
    rcases z with ⟨a,b⟩; have hp: affine invS 0 a= -a:=by rw [affine,add_zero];ext i; simp [invS,Signed.act]
    unfold sendEdge;rw [hp];rfl
 rw [if_pos (show invS.flip z.2=true from rfl),ht]; rw [show (snow G v).fst=Geometry.reco v.fst from rfl,reco_edge]; rfl

lemma snow_dot (x y:Vec G n 1): snowU G n x ⬝ᵥ snowU G n y=x ⬝ᵥ y:=by
 unfold dotProduct snowU;simp_rw [neg_mul_neg]; exact Equiv.sum_comp (iceE G n) (fun i=>x i*y i)
lemma turns_i (x): snowU G n (Pi.single x 1)= -Pi.single (iceE G n x) 1:=by
 ext1 i; have hp : i=iceE G n x ↔ iceE G n i=x:= ⟨fun h=>by rw [h,ice_i],fun h=>by nth_rw 1 [← ice_i G n i];rw [h]⟩
 by_cases hv:i=iceE G n x
 · subst i; simp [snowU,ice_i]
 simp [Pi.single_apply,snowU,hv]; exact mt hp.mpr hv
lemma map_i (i: FreeResolvent.Slot G n 1)(M:Matrix (FreeResolvent.Slot G n 1) A ℝ)(j:A) [Fintype A] : snowU G n (Pi.single i 1) ⬝ᵥ (M*ᵥ (Pi.single j 1))= -M (iceE G n i) j := by rw [turns_i,neg_dotProduct,dotProduct_comm,dotProduct_single_one]; exact congr_arg Neg.neg (dotProduct_single_one ..)
lemma pair_i (x: FreeResolvent.Slot G n 1)(M:Matrix (FreeResolvent.Slot G n 1) (FreeResolvent.Slot G p 1) ℝ)(j) : snowU G n (Pi.single x 1) ⬝ᵥ (M*ᵥ snowU G p (Pi.single j 1))= M (iceE G n x) (iceE G p j) := by rw [turns_i G p,Matrix.mulVec_neg,dotProduct_neg,turns_i G n,neg_dotProduct,dotProduct_comm,dotProduct_single_one,neg_neg]; exact dotProduct_single_one ..
lemma row_i (x: FreeResolvent.Slot G n 1)(M:Matrix (FreeResolvent.Slot G n 1) (FreeResolvent.Slot G p 1) ℝ)(j) : (Pi.single x 1) ⬝ᵥ (M*ᵥ (Pi.single j 1))=M x j:=by rw [dotProduct_comm,dotProduct_single_one];exact dotProduct_single_one ..
lemma existsU (x:FreeResolvent.Vec G n 1):∃ f:Bid.Dir G n,x=FreeResolvent.flatten f:=⟨fun i=>WithLp.toLp 2 (fun j=>x (i.1,i.2,j)),rfl⟩
-- loop
variable {n} (B:Precision.Bed){σ Ω α:ℝ}{S:Clip}(F:Hall B σ Ω α S)(Q:∀ n,Bid.Sworn B n G)
include F Q
lemma tune_s : Flurry (crust G B)=crust G B:=by
 apply frosting _ _ _ (crust_f G B F.stripP.2.1 F.pos.le F.paid) _ (crustA G B)
 intro n i j; simp_rw [← snow_ice,crust_id G B F.stripP.2.1 F.pos.le]
 let M:= tensor G (Precision.K (B.metric.acts n)); let k:=(linksQ G).swrap n i;let p:= (linksQ G).swrap n j
 change M k p=M (iceE G n k) (iceE G n p);rw [← row_i G n k M p, ← pair_i G n k M p]
 obtain ⟨a,ha⟩:= existsU G n (Pi.single k 1); obtain ⟨b,hb⟩:=existsU G n (Pi.single p 1)
 rw [ha,hb,← where_about,← where_about]
 have he (a b: Bid.Dir G n): FreeResolvent.flatten a ⬝ᵥ (M*ᵥ FreeResolvent.flatten b)=Bid.gaugeFiscal B a b:=by
    unfold M; rw [FreeResolvent.component_dot];simp_rw [FreeResolvent.component_mul];rfl
 rw [he,he,Q n invS]

omit F Q
lemma snowed_K (P:Patch)(K:KernelChoices)(V:P.Branches K G):Flurry (OrthoQ P K G)=OrthoQ P K G:=by
 apply frosting (linksQ G) (blockQ G P.L) _ ((priced_D P K G 0).buys le_rfl).1 _ (stampD P K G)
 intro n i j; rw [← snow_ice, ← snow_c, credited];
 let F:= avenue P K n;let M:= FreeResolvent.tensor G (probe F);let h:= (linksQ G).swrap n i;let t:= (blockQ G P.L).swrap n j
 change M h t=M (iceE G n h) (iceE G (n*P.L) t);rw [← row_i G n h M t,← pair_i G n h M t];
 have hE (u:Bid.Dir G (n*P.L)): M*ᵥ FreeResolvent.flatten u=FreeResolvent.flatten (Bid.bills F u):=by
    ext1 p; change component (G:=G) (tensor G _ *ᵥ FreeResolvent.flatten u) p.2.2 (p.1,p.2.1)= (Bid.bills F u (p.1,p.2.1)) p.2.2
    rw [FreeResolvent.component_mul];rfl
 obtain ⟨u,hu⟩:=existsU G (n*P.L) (Pi.single t 1);rw [hu,← where_about,hE,hE, bills_signed invS V u,where_about,snow_dot]
end YM.RegulatorIR.Oracle
