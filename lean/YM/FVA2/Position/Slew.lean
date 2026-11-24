import YM.FVA2.Position.Wheel
import YM.FVA2.Press.Subtraction
/-!
# Physical programs equivariant at ALL levels; no adjustments changed stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.Wheel
open Function Set Filter Finset Lattice Wilson
open MS MS.Koszul MS.Plane MS.Book MS.Native MS.Native.Orient MS.Native.Chart
open MS.Native.Sew MS.Cylinder MS.Cylinder.Lab MS.Landau MS.Color MS.Native.Paint
open MS.Momentum MS.Menus MS.Native.Wilsonian MS.Arts MS.Outlook
open MS.Book.Program MS.Book.Convolve Brass Labels Press Axes Source Source.Drops Bid XSpace RG
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {J:Type}{m n d:ℕ}{G:Gauge}(s: Signed) {𝓐:Hol G}(A:Survey G 𝓐 d)
local notation "Z₀"=> knot A
lemma read_p (p:Pol G)(X:CoverConfig G): Press.wheel A p (Lattice.pull s 0 X)= Press.wheel A (rotated s.ortho p) X := by change Labels.read (expand d (A.reading _)) _=_; rw [A.reading_signed,snap_expand]; exact ( eval_changed .. ).symm
lemma offers (p:Pol G)(n:Side)(X:Config G n): offered A p n (Lattice.pull s 0 X)=offered A (rotated s.ortho p) n X:=by unfold offered; rw [expandAt_pull,Lattice.affine,Signed.act_zero, add_zero, read_p]
lemma boarded (p:Pol G): pose s (Press.dot A p)= Press.dot A (rotated s.ortho p):= by
    refine (markEq ..).mp (Eventually.of_forall fun n=>?_); apply Subtype.ext; rw [travel_t]; let X:= offered A p n ∘ nation; rw [show shown n (Press.dot A p)=region.symm (reads X) from Subtype.ext (billed A p), pose_rule s (hot_σ A p), show ( X ∘ Orient.affine s)= offered A (rotated s.ortho p) n ∘ nation from ?_ ]; exact (billed A _).symm
    unfold X; funext i; rw [comp_apply,comp_apply,at_nation, offers]; rfl
def red : Pol G→ₗ[ℝ] Dot G Cover where
   toFun p:= Press.dot A p
   map_add' f g:= by unfold Press.dot; rw [show Press.pigment A (f+g)= Press.pigment A f + Press.pigment A g from funext fun x=> by simp [Press.pigment,Press.window,wheel] ]; exact add_art A ( pigment_hot A f|>.contDiffAt) (pigment_hot A g|>.contDiffAt)
   map_smul' x a:= by unfold Press.dot; rw [show Press.pigment A (x • a)=x • Press.pigment A a from ?_ ]; exact smul_art A x (pigment_hot A a|>.contDiffAt); funext p; -- real convention on v
                       unfold Press.pigment Press.window; rw [comp_apply, wheel, show x • a=(x:ℂ) • a from (IsScalarTower.algebraMap_smul ℂ x a).symm, map_smul ]; simp [wheel]
local notation "H" => Press.portDeck G
abbrev sample (G:Gauge) := XSpace.Initialize G
variable (Y: XSpace.Initialize G)
local notation "𝓡"=> Press.wickInput Y
private lemma cc (x:ℝ)(f:Pol G) : (x:ℂ)•f=x • f:= IsScalarTower.algebraMap_smul ℂ x f
lemma μ_box (i:Case G m n): Labels.tensor s.ortho (beginning i)= ∑ j:Case G m n, (markS s G m n i j:ℂ) • beginning (w:=m) j:= by refine Subtype.ext ?_; rw [ AddSubmonoidClass.coe_finsetSum ]; simp_rw [Submodule.coe_smul, cc ]; exact Axes.cast ..
lemma wed (g:Glyph H d)(k:g.Bundle): Labels.tensor s.ortho (chip Y g k)=∑ j:Case G g.size g.grade,( markS s G g.size g.grade g.2.2 j:ℂ ) • chip Y (Axes.take g j) k := by
   cases k with | inl a=> exact μ_box s _ | inr a=>
      simp only [ chip,Sum.elim_inr ]; rw [← gradePart_turn, Press.diff, map_sub, ← XSpace.Survey.wick_signed, μ_box ]; simp only [map_sub,map_sum,map_smul, Press.diff,smul_sub,Finset.sum_sub_distrib ]; try rfl
lemma frost_ang (c:Glyph H d) (k:c.Bundle): pose s (c.hand (wickInput Y) k)=∑ j:Case G c.size c.grade,markS s G c.size c.grade c.2.2 j • Glyph.hand (wickInput Y) (Axes.take c j) k:= by
   have he := wed s Y c k; simp_rw [ stampF ]; rw [boarded, show rotated s.ortho ( Press.chip Y c k ).val= _ from congr_arg Subtype.val he]; let f(i:Case G c.size c.grade) : Label G c.size:= chip Y (Axes.take c i) k; let l(i: Case G c.size c.grade):ℂ:= markS s G c.size c.grade c.2.2 i; change dot (Y.surveys c.size) (Labels.localFields G c.size |>.subtype (∑ i,l i • f i))= _; rw [map_sum]; change red (Y.surveys c.size) (∑ i: Case G c.size c.grade, _) = _; rw [map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [ map_smul ]; unfold l; simp_rw [cc]; exact map_smul (red _) _ _
lemma gallery_s (c:Glyph H d): pose s ∘ Glyph.gallery (wickInput Y) c= rotateField s (Glyph.gallery (wickInput Y)) c:= by
 funext i; simp_rw [rotateField,Glyph.gallery, comp_apply, Finset.sum_apply,Pi.smul_apply, map_sum,Book.levels,poseModel,frost_ang,map_sum]; rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_apply, Finset.smul_sum]; refine Finset.sum_congr rfl (fun k _=>?_ ); exact map_smul ((( Book.model ((i:ℤ)+(c.tally k:ℤ)):Dot G Cover→ₗ[ℂ] Dot G Cover )).restrictScalars ℝ) _ _
lemma preamble_s (c:Glyph H d)(p:Team)(x:ℝ): pose s ∘ Glyph.preambleF (wickInput Y) p c x= rotateField s (fun i=>Glyph.preambleF (wickInput Y) p i x) c:= by
 unfold Glyph.preambleF; rw [← wobPose, gallery_s]; unfold rotateField; rw [map_sum]; exact Finset.sum_congr rfl (fun j _=> map_smul ( (wobble G p x).restrictScalars ℝ) _ _)
end YM.FVA2.Position.Wheel
