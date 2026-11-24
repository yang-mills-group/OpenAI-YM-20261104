import YM.RegulatorIR.Oracle.Moments

/-! Preserve pre-cost on meteor. Symmetric averaging only for the gradient
pattern, see Δ/Y to use usual $A0$ pointwise in bulk call. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge} {X Y A B : Type}{α σ σ' Ω Ω' δ δ' r l s:ℝ} {q:ℕ} {n t: Side}

section sealP
variable (P:Patch)(K:KernelChoices)(B B':Precision.Bed)(G:Gauge)(R:Cross P.L (TypeFace 1) (TypeFace 1))
-- Spur gauge orientation when both Φ and A flipped. sign precisely as in gauge convention.
def surge (F: RegulatorIR.Gain.Bride G):RegulatorIR.Gain.Bride G:=fun x y=> - F (-x.1,x.2) (snow G y)
lemma rolled (F: Layer (Long G.ColorIndex) (Long G.ColorIndex))(V:RegulatorIR.Gain.Bride G): Gain.valve (Flurry F) (surge G V)=Flurry (Gain.valve F V):=by
 funext x y; let u:=x.1.1;let f:= x.1.2; let i:=x.2
 unfold Gain.valve Flurry surge; dsimp only;rw [neg_sub_neg,show (snow G x).fst.snd=f from rfl, show (snow G x).snd=i from rfl, show (snow G x).fst.fst= -u-step f from rfl]; rw [sub_add_cancel]; rw [show -(x.1.1+step x.1.2)= -u-step f from by unfold u f; abel]
lemma turn_P (F: RegulatorIR.Gain.Bride G): surge G (surge G F)=F:=by ext1 i;ext1 j; unfold surge; simp [flinty]
def conveyer := (1/2:ℝ) • (phiQ P K R G+surge G (phiQ P K R G)) -- alias Φ' 
def starrier := (1/2:ℝ) • (ruling P G R+Flurry (ruling P G R))
lemma inv_L : Flurry (starrier P G R)=starrier P G R:=by
 ext1 x; ext1 y; unfold starrier Flurry; simp only [Pi.add_apply,Pi.smul_apply,flinty]; rw [add_comm]
lemma inv_V : surge G (conveyer P K G R)=conveyer P K G R:=by
 ext1 x;ext1 y; unfold surge conveyer; simp only [surge,Pi.smul_apply,Pi.add_apply, flinty,neg_neg]; rw [← smul_neg];simp only [neg_add]; abel
lemma albe_U : Albedo (blockQ G P.L) (linksQ G) (starrier P G R):=by
 have he:= albedoX P R G; refine Albedo.smul (Albedo.add he ?_) _
 intro i j d; unfold Flurry; rw [strut,site_roll,drift_f,drift_f,← smul_neg,←strut,← site_roll]; exact he ..
lemma albe_V : Albedo (gardens P G) (linksQ G) (conveyer P K G R):=by
 have he:= albedoQ P K R G; apply Albedo.smul (Albedo.add he _) _
 intro i j d; unfold surge; apply congr_arg Neg.neg; rw [site_roll,drift_f,c_shift,← site_roll];
 let x:RegulatorIR.Gain.Point G:= (-i.1,i.2); rw [show (-(P.L.val • d+i.1), i.2)=(gardens P G).shiftB (-d) x from ?_] -- simp β
 exact he ..
 rw [c_shift]; simp only [smul_neg,neg_add];rfl
variable {S S':Clip}
lemma sets (F:Hall B σ Ω δ S)(C:Hall B' σ' Ω' δ' S')(h:BidP P K B B' R σ α)(Z:P.Branches K G)(A:∀ n,Bid.Sworn B n G): projectionQ P K R G=Gain.valve (starrier P G R) (conveyer P K G R):=by
 have ht:= restoring P K G B B' R F C Z h A
 rw [← show (1/2:ℝ) • (projectionQ P K R G + projectionQ P K R G) = projectionQ P K R G from funext (fun i=> funext (fun j=>by simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring))];
 nth_rw 1 [← ht]; rw [projectionQ,← rolled]; unfold starrier conveyer; ext1 i; ext1 j; simp only [Pi.add_apply,Pi.smul_apply,Gain.valve,smul_eq_mul];ring
lemma pipes (h:Even n.val)(hv:l*n.val=s): Gain.Rune (Carto G l s h hv) (n*P.L) (conveyer P K G R):=by
 let W:= conveyer P K G R; have he (x:Cover)(p:Cover)(y:Long G.ColorIndex)(i:G.ColorIndex) : W (P.L.val • p+x,i) (motionsQ y p)=W (x,i) y:=by
    rw [← site_roll]; exact Eq.mp (by rw [← c_shift (A:=G.ColorIndex) (x:=(x,i)) P.L p]) (albe_V P K G R (x,i) y p)
 have hz(v:Cover) : (n*P.L).val • v=P.L.val • n.val • v:= by rw [smul_smul,Nat.mul_comm P.L.val];rfl
 rintro (v|v) x y i
 · change W (x+(n*P.L).val • v,i) (motionsQ y _)=1* _; rw [hz,add_comm]; exact (he ..).trans (one_mul ..).symm
 change W (-x+(n*P.L).val • v,i) (motionsQ (snow G y) _)=(-1)*W (x,i) y; rw [hz,add_comm, he,neg_one_mul]
 have hp:= congr_fun (congr_fun (inv_V P K G R) (x,i)) y; change -W (-x,i) (snow G y)=_ at hp; change -W _ _=W (x,i) y at hp;linarith
end sealP
end YM.RegulatorIR.Oracle
