import YM.RGComparison.Core16.Lam.Fold
/-!
# Θ-near stencil of the mayor moments. No Θ-choice coincidence conditions at GS.calculator beyond masks. Ward.K evaluation
before transporting winding logic through gauges. Growth grants AFTER patch locale. Critical t.L shape prescribed by owner. Includes all auxiliary register cost data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {P: Patch} {K:KernelChoices} {d:f.val=c.val*P.L.val}
    (W:Oven P)(X:Shelf G (PlaqAxes⊕Axis) W.Xways)

variable {ι k T:Type}
def stock (P:Planet X f ι k T)(a:k) : Stuff G ι W.Xways:= fun i=>(P.stem a i).elim (.inr 0) Sum.inl -- type params declare

def reporter (W:Oven P)(K:KernelChoices)(t:Axis) (y:W.Xways→G.Color): G.Mat:= let S:= W.stance K; G.mat ((S.prediction (W.lamp (0,y)) (Classical.arbitrary S.Choices) (0,t))⁻¹)

def plate (W:Oven P)(K:KernelChoices)(x:G.Color)(j:Axis) (y:W.Xways→ G.Color) := line1 (Lam.over K (reporter W K j y)) 0 x
def tops (W:Oven P)(K:KernelChoices)(x y:G.Color)(j:Axis) (p:W.Xways→ G.Color) := lend (Lam.over K (reporter W K j p)) x y

set_option quotPrecheck false
local notation "S"=> StepData.mk P K d
local notation "M"=> W.stance K
variable (hK:P.Branches K G)
include hK
lemma rays (j:Axis) : reporter W K j (0:W.Xways→ G.Color)=1 ∧ ContDiffAt ℝ ω (reporter W K j (G:=G)) 0:=by
     constructor
     · unfold reporter; dsimp only; rw [show ((0,(0: W.Xways→ G.Color)):Lumen.Point G _) = 0 from rfl,W.lamp_zero, Push.settled (W.stance K) hK,inv_one,G.mat_one]
     unfold reporter; dsimp only; let m : Point G W.Xways := (0,(0:W.Xways→G.Color)); let h:=(Push.prediction_cont M hK (0,j) (Classical.arbitrary (W.stance K).Choices)); simp_rw [G.mat_inv, W.lamp_eq]
     apply (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp; let T (v: Push.In G W.floor):= G.mat ((M).prediction (represent v) (Classical.arbitrary (M).Choices) (0,j)); have hx:ContDiffAt ℝ ω T (W.logs m):= W.logs_zero.symm ▸ h; refine hx.comp (f:=fun y : W.Xways→ G.Color=> W.logs (0,y)) _ ?_; exact W.logs_hot.comp (f:=fun y:W.Xways→G.Color=>((0,y):Point G _)) _ (contDiffAt_const.prodMk (f:=fun _=>(0:G.Color)) (g:=id) contDiffAt_id)
lemma public_plate (i j:G.Color)(p:Axis): ContDiffAt ℝ ω (plate W K i p) 0 ∧ plate W K i p 0=0 ∧ ContDiffAt ℝ ω (tops W K i j p) 0 := by
    obtain ⟨hx,he⟩:= rays W hK p; exact ⟨(swirl K i).contDiffAt.comp _ he,by rw [plate,hx]; exact slope_zero .., (tilt K i j).contDiffAt.comp _ he⟩

variable {W X}
variable (hW: Parcel.Oven.Offers W X K)(B:Forest (StepData.mk P K d).ratio) (h:P.Branches K G)
local notation "U"=> gear S B X
omit hK
include hW
-- map bought before nominal patches for all N,K. needs no Big proof c lower bound (coarse patch wraps), fine sector cost independent from hC≥2. Anchor.u≥ etc. near term independence for ALL i in common T.θ irrespective posterior event.
omit hW in
lemma stamped_signal (j:Hut.Rooms c f)(p:Sky G B.Free){g:ℝ}(hg:0<g) : g • book (stock W X U j) g p=((U).load j g p).2 := by
    funext i; change g • book (stock W X U j) g p i = portrait ((U).stem j) (fun i=> G.curvature (p i)) i; unfold book stock portrait; cases hx: (U).stem j i with
    | none=> simp
    | some u=> exact smul_inv_smul₀ hg.ne' _

include h
lemma chooses (j:Bond c)(z: Sky G B.Free){g:ℝ}(hg:0<g)(he: amen X g)(hz: crisp X.δ ((U).soil (.inr j)) z) (t:(S).Choices) :
   around S B t z j= Lam.reporter W K j.2 (g • book (stock W X U (.inr j)) g z) := by
    -- align cover patch stocks
    let X':= U; let i: Hut.Rooms c f:= .inr j; let p:= X'.load i g z; let v:= B.drape z; let J:= W.lamp p; let a : Bond W.roof:= (0,j.2); let T := S; let r:=(Classical.arbitrary (M).Choices)
    have A:(0,(g•book (stock W X U i) g z))=p:= (Prod.ext (show p.1=0 from smul_zero g) (stamped_signal (W:=W) B i z hg).symm).symm
    have hp: clasp (expandAt (hold S j.1) v) (expandAt (hold M 0) J) (Hut.width P):= oiled B hW i (u:=0) (g:=g) hz
    have hz:‖p‖≤X.R:= load_ok B hW (fun i=>show ‖(0:G.Color)‖≤ _ from norm_zero.trans_le hW.good.thick.1.le) he i hz
    have he:=hW.illustration p (mem_closedBall_zero_iff.mpr hz)
    let w : (M).Choices:= (fun z=> if z=a.1 then t.1 j.1 else t.1 (j.1+step j.2), fun _=> t.2 j)
    have ht : a.1+step a.2≠a.1:= YM.FreeResolvent.Affine.View.next_step _ W.odd_width
    have hh: T.connector v t.1 j=(M).connector J w.1 a:= carries K W h hp t.1 w.1 (if_pos (Eq.refl (0:Site W.roof))|>.symm) (if_neg ht|>.symm) -- hp variable renamed
    unfold reporter around; dsimp only; change G.mat ((T.prediction v t j)⁻¹)= G.mat (((M).prediction (W.lamp _) r a)⁻¹); rw [A, show (M).prediction _ r=(M).prediction J w from he.same ..,StepData.prediction,StepData.prediction,hh]; rfl
end YM.RGComparison.Core16.Lam
