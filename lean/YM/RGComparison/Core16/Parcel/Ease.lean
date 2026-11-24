import YM.RGComparison.Core16.Parcel.Funding
import YM.Push.FREE_RESOLVENT.Views
/-!
# On the Wilson STEP. output → Planet, family of actual parameters g exp.

Invoices usable after local post-block prescriptions, arbitrary period including winding. Surveyed
price (kernel level seam) BEFORE contour. Need budget chart-price locations per cool stencil; keeps
equivalent occurrences. No trace continuation estimates or declaration of completion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Parcel.Oven
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Matrix Push.AbsoluteSums.Animals
open Lumen Lumen.Planet PertExtension PertExtension.Series Tested Radial Therm
open Forge Forge.Hut Precision Exterior Push Push.BetaTransport Push.GridApprox Finset
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side}{H:Patch}(K:KernelChoices)
variable {d:f.val=c.val*H.L.val}
variable {P:Oven H}(X:Shelf G (PlaqAxes ⊕ Axis) P.Xways)
local notation "S"=> StepData.mk H K d
local notation "S0"=> P.stance K
local notation "R"=>Hut.width H

variable (T:Forest (StepData.mk H K d).ratio) (u:Directions G c)

def slice (g:ℝ) : Config G c:= fun i=>G.lieExp (g • u i)
set_option trace.Meta.debug false in
def parcela : Planet X f T.Free (Rooms c f) (S).Choices :={
    loc:= Hut.pad T
    root:=root S
    meter _ x w:= (S).likelihood (T.drape w) x
    cost := show (ℝ→ (S).Choices → Sky G T.Free → Rooms c f→ℝ) from fun g=>((Hut.seam (G:=G) S T (slice (G:=G) u g) : Base G f T.Free (Rooms c f) (S).Choices)).cost
    glyph := Sum.map Prod.snd Prod.snd
    stem i:= P.listPtr K T (root S i)
    ray := Sum.elim (fun _=> 0) u }
variable {K X u}(hp:P.Offers X K)(hu:∀b,‖u b‖≤X.Q)
local notation "Y"=> parcela K X T u
include hp hu

omit hu hp in
lemma handed (g:ℝ):(Y).F g= Hut.seam S T (slice u g):=rfl
lemma budgeting (i: Rooms c f): ‖(Y).ray i‖ ≤ X.Q:=by rcases i with i|i; exact (show ‖(0:G.Color)‖=0 by simp).le.trans hp.good.thick.1.le; exact hu _
omit hu in
private lemma inception : X.sector.b= R:= by obtain ⟨Q,h,r,-⟩:= hp.purchase; rw [r]; rfl
omit hu in
lemma geometry (i: Rooms c f): (Y).soil i=neighborsOf (Hut.pad T) R (root S i):= congrArg (fun t=> neighborsOf (Hut.pad T) t _) (inception hp)
omit hu in
lemma spirit (a:Rooms c f)(p:P.Xways)(i:T.Free) (hi:(Y).stem a p=some i): i∈ (Y).soil a:= by rw [geometry T hp]; exact thread _ _ _ _ _ hi

variable {x:Sky G T.Free}{g:ℝ} (hg:amen X g)(i:Rooms c f)(hc:crisp X.δ (((parcela K X T u).soil i)) x)
include hg hc
lemma load_ok : ‖(Y).load i g x‖ ≤ X.R := by
    unfold Planet.load; rw [Prod.norm_def,norm_smul]; refine max_le ?_ ?_
    · rw [Real.norm_of_nonneg hg.1]; exact (mul_le_mul hg.2 (budgeting T hp hu i) (norm_nonneg _) hp.good.thick.2.1.le).trans hp.good.thick.2.2.le
    rw [pi_norm_le_iff_of_nonneg hp.good.positive.le]; intro d; change ‖portrait ((Y).stem i) _ d‖ ≤ _; unfold portrait; rcases he:(Y).stem i d with _|j
    · exact (show ‖(0:G.Color)‖=0 by simp).le.trans hp.good.positive.le
    exact ((G.curvature_norm _).trans_lt ((hc j (spirit T hp (u:=u) i d j he)).trans hp.good.extent.2)).le
omit hu hg in
lemma oiled : clasp (expandAt (root S i) (T.drape x)) (expandAt (hold S0 0) (P.lamp ((Y).load i g x))) R := by
    rw [geometry T hp] at hc; exact fun _ hv j=> tipfill _ _ ((parcela (P:=P) K X T u).load _ _ _) rfl hc hp.good.reenter hv j
omit hc
lemma glow (hS:H.Branches K G)(b: Bond c) (t:(S).Choices)(hc:crisp X.δ ((Y).soil (.inr b)) x):
   (P.actual K (Sum.inr b.2) ((Y).load (.inr b) g x) = (Y).cost g t x (.inr b)) ∧ H.frameMass K (expandAt (hold S b.1) (T.drape x)) (t.1 b.1)=(Fintype.card H.FrameTag:ℝ)⁻¹ ∧
      H.predictorMass K ((S).connector (T.drape x) t.1 b) (t.2 b)= (Fintype.card H.Points:ℝ)⁻¹ := by
      let a: Bond P.roof := (0,b.2); let i:Rooms c f:= .inr b; let M:= T.drape x; let Λ:= (Y).load i g x; let W:= P.lamp Λ
      have he:a.1+step a.2≠a.1:=FreeResolvent.Affine.View.next_step _ P.odd_width
      let w : (S0).Choices:= (fun z=> if z=a.1 then t.1 b.1 else t.1 (b.1+step b.2), fun _=> t.2 b)
      have hp' : clasp (expandAt (hold S b.1) M) (expandAt (hold S0 0) W) R:=oiled T hp i (g:=g) hc
      have hR : Agrees (Lattice.box (reach H):Set Cover) (expandAt (hold S b.1) M) (expandAt (hold S0 0) W):=fun i h _=> hp' _ (box_larger h (by unfold Hut.width; omega)) _
      have br:=hp.illustration Λ (mem_closedBall_zero_iff.mpr (load_ok T hp hu hg i hc))
      have hl:=hS -- add
      have hi : (S).connector M t.1 b=(S0).connector W w.1 a:= carries K P hl hp' t.1 w.1 (if_pos (Eq.refl (0:Site P.roof))|>.symm) (if_neg he|>.symm)
      refine ⟨?_,((patch_dep H hl _ hR).2).trans (br.stores ..),?_⟩; rotate_left
      · change H.predictorMass K ((S).connector M t.1 b) _=_; rw [hi]; exact br.conn ..
      change linkEnergy S0 (G.lieExp Λ.1* ((S0).prediction W (Classical.arbitrary _) a)⁻¹)=linkEnergy S (G.lieExp (g • u b)* ((S).prediction M t b)⁻¹)
      change _= linkEnergy S0 (G.lieExp Λ.1* ((S).prediction M t b)⁻¹)
      rw [show (S0).prediction W (Classical.arbitrary _)=(S0).prediction W w from br.same ..,StepData.prediction,StepData.prediction,hi]; rfl
end YM.RGComparison.Core16.Parcel.Oven
