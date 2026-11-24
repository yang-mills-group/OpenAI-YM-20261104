import YM.Integration.WilsonPositionProgramTrialPublicJointFirstReturn
import YM.Integration.WilsonPositionProgramTrialPublicJointFirstScore
import YM.Integration.WilsonOriginalPublicFigureWickFaces
/-! The first fitted physical answer and the publicly projected stencil at the same visited sites. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFirstSource
open Lattice RG Tree XSpace XSpace.Cirrus XSpace.Rose Labels
open Finset PowerSeries Next.Rank.Normal PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos Precision
open WilsonIndependentMatchedNamedPair (printed)
open WilsonIndependentRawRosterWord (film fold)
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonOriginalPublicNodalBufferedCellRow (Stamps Frames)
open WilsonPositionProgramTrialPublicJointFirstReturn (wilson)
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(d:Fin (n+1)→ℕ)(Y:Sample 2)

theorem count {I A:Type}[CommMonoid A](V:I→A)(n:ℕ)(sel:Fin (n+1)→I):
    WilsonIndependentRawRosterWord.fold V (branch n sel)=∏i,V (sel i):=by
  induction n with
  | zero=>simp [branch,WilsonIndependentRawRosterWord.fold]
  | succ n ih=>rw [branch,WilsonIndependentRawRosterWord.fold,Fin.prod_univ_succ,ih];rfl

def site (z:Fin (n+1)→Lattice.Cover):Sample (n+1):=⟨Y.F,z,Y.center⟩
def axis (a:Stamps R d)(i:Fin (n+1)):(Frames R d i).Coeff:=
  (Frames R d i).coords ((Frames R d i).basis (sheet (Frames R d i) (a i)))
def label (side:Bool)(z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(i:Fin (n+1)):Bare.Series (W.tree Y.F.p) G:=
  printed R W Y side (d i) (z i) (sheet (Frames R d i) (a i))
def projected (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(K:ℕ)(i:Fin (n+1)):Bare.Series (W.tree Y.F.p) G:=
  WilsonOriginalPublicFigureWickFaces.ordinary R W d (axis R d a) (site Y z) K i
def surplus (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(i:Fin (n+1)):Bare.Series (W.tree Y.F.p) G:=
  WilsonOriginalPublicFigureWickFaces.surplus R W d (axis R d a) (site Y z) i

theorem refiled (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(K:ℕ)(i:Fin (n+1)):
    label R W d Y true z a i=projected R W d Y z a K i+surplus R W d Y z a i:=by
  have earn:=WilsonOriginalPublicFigureWick.priced_word W (Frames R d i) (site Y z)
    (R.family.S.a K) (R.family.S.a_pos K).ne' (chartV (site Y z) i) (axis R d a i)
  rw [add_assoc] at earn
  simpa only [projected,surplus,site,WilsonOriginalPublicNodalBufferedCellRow.Frames,chartV,Function.comp_apply,WilsonOriginalPublicFigureWickFaces.ordinary,
    WilsonOriginalPublicFigureWickFaces.surplus,label,printed,if_true,axis,LinearEquiv.symm_apply_apply] using earn

def rawChange (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d):Bare.Series (W.tree Y.F.p) G:=
  (∏i,label R W d Y false z a i)-∏i,label R W d Y true z a i
def offshell (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(K:ℕ):Bare.Series (W.tree Y.F.p) G:=
  (∏i,(projected R W d Y z a K i+surplus R W d Y z a i))-∏i,projected R W d Y z a K i

def wick {P:XSpace.Period}(T:P.Tree)(A:Bare.Series T G)(q:ℕ):ℂ:=
  let g:=blend (Bare.Q T G) 0
  let score:=WilsonPositionProgramTrialPublicJointFirstScore.score T G
  if q=0 then g (constantCoeff A) else g (coeff 1 A+score*constantCoeff A)-g score*g (constantCoeff A)

theorem low {P:XSpace.Period}(T:P.Tree)(A:Bare.Series T G)(q:ℕ)(hit:q≤1):
    coeff q (Bare.normalized T G A)=wick T A q:=by
  have paid:=WilsonPositionProgramTrialPublicJointFirstScore.original T G A
  interval_cases q
  · rw [coeff_zero_eq_constantCoeff]; exact paid.1
  · exact paid.2

theorem original (z:Fin (n+1)→Lattice.Cover)(a:Stamps R d)(K q:ℕ)(hit:q≤1):
    wilson R W (fun _=>false) d Y z a q-wick (W.tree Y.F.p) (∏i,projected R W d Y z a K i) q =
      wick (W.tree Y.F.p) (rawChange R W d Y z a) q+wick (W.tree Y.F.p) (offshell R W d Y z a K) q:=by
  simp only [←low _ _ q hit]
  unfold wilson film
  rw [count]
  change coeff q (Bare.normalized _ G (∏i,label R W d Y false z a i))-_ = _+_
  unfold offshell
  simp_rw [←refiled R W d Y z a K]
  unfold rawChange
  simp only [map_sub]
  ring

end YM.Integration.WilsonPositionProgramTrialPublicJointFirstSource
end
