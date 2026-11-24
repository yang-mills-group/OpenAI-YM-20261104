import YM.Integration.WilsonGeneralArityCopyAccount
import YM.Integration.WilsonOriginalPrimerStampedRay
import YM.Integration.WilsonOriginalPrimerReceipts

/-! The literal group print at a flat field is exactly its finite
zero-angular coupling polynomial. The argument uses the saved copy and its
own chart, including the constant of every marked mode. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatCopy
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open PertExtension PertExtension.Series Radial AllOrder.Laplace AllOrder.Laplace.SigmaP Response
open AllOrder.Ink AllOrder.Ink.Method WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada
open WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonGeneralArityCopyAccount WilsonOriginalPrimerReceipts WilsonOriginalPrimerStampedRay
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{d q:ℕ}{σ:ℝ}

private theorem clear {k:ℕ}(t:Atom G k)(pos:0<k)(o:Site n):
    t.unmasked (1:Config G n) o=0:=by
  have face (c:Face (Per n)):faceValue (1:Config G n) c=1:=by simp [faceValue,Lattice.square]
  have leg (s:RG.Slot):s.atSite (1:Config G n) o=0:=by
    rw [Work.F03.atSite_path,face,G.curvature_unit,map_zero]
  unfold Atom.unmasked Atom.poly
  apply Finset.sum_eq_zero
  intro z _
  have hz : (t.leg ⟨0,pos⟩).atSite (1:Config G n) o (z ⟨0,pos⟩)=0:=by rw [leg]; rfl
  rw [Finset.prod_eq_zero (Finset.mem_univ (⟨0,pos⟩:Fin k)) hz,mul_zero]

private theorem jet_zero (f:Link G n→ℝ){r:ℕ}(pos:0<r):Radial.jet f r (0:Link G n)=0:=by
  unfold Radial.jet
  rw [(iteratedFDeriv ℝ r f 0).map_coord_zero (⟨0,pos⟩:Fin r) (m:=fun _=>0) rfl]
  simp

private theorem head_zero (Y:Lantern G Unit)(o:Site n)(j e:ℕ):
    head Y o j e (0:Link G n)=if j=e then Y.atom.unmasked (1:Config G n) o else 0:=by
  unfold head
  by_cases le:j≤e
  · rw [if_pos le]
    by_cases same:j=e
    · subst e
      simp only [Nat.sub_self,Nat.zero_add,if_true]
      by_cases z:Y.r=0
      · calc
          _=Radial.jet (Helmet.frame Y.atom o) 0 (0:Link G n):=congrArg (fun k=>Radial.jet (Helmet.frame Y.atom o) k (0:Link G n)) z
          _=_:=by simp [Radial.jet,Helmet.frame]
      · rw [clear _ (Nat.pos_of_ne_zero z)]
        exact jet_zero _ (Nat.pos_of_ne_zero z)
    · rw [if_neg same]
      have pos:0<e-j+Y.r:=by omega
      exact jet_zero _ pos
  · rw [if_neg le,if_neg (fun same=>le same.le)]

def grade (T:Copy G d q σ)(o:Site n)(j:Fin (q+1)):ℝ:=
  ∑'a:{i:(T.roll j).Ty//0<((T.roll j).leg i).atom.magnitude},
    ((T.roll j).leg a.val).atom.unmasked (1:Config G n) o

theorem folded (T:Copy G d q σ)(σpos:0<σ)(o:Site n)(l e:Fin (q+1)):
    ((T.roll l).folded l e).table n (mingle (0:Link G n) (WilsonElectedPrimaryTensor.pin o)) =
      if l=e then grade T o l else 0:=by
  have earned := WilsonOriginalPrimerReceipts.located (T.roll l) l d e T.positive
    (mul_pos (by norm_num) σpos) (T.paid l) o (0:Link G n)
  rw [←earned.tsum_eq]
  by_cases same:l=e
  · subst e;simp only [head_zero,if_true];rfl
  · have diff:l.val≠e.val:=fun h=>same (Fin.ext h)
    simp only [head_zero,if_neg diff,tsum_zero,if_neg same]

theorem original (T:Copy G d q σ)(σpos:0<σ)(o:Site n)(g:ℝ)
    (Z:∀n:Side,Site n→PChart G n)(book:Matched T Z):
    ∑'z:T.Roster,term T o g (1:Config G n) z =
      ∑j:Fin (q+1),(g^j.val*MvPolynomial.eval (0:Link G n) (coeff j (flash (Z n o))):ℝ):=by
  rw [(absolute T o σpos.le g 1).tsum_sigma,tsum_fintype,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  have eq:=book j (by omega) n o (0:Link G n)
  simp_rw [folded T σpos] at eq
  rw [Finset.sum_ite_eq'] at eq
  rw [eq,if_pos (mem_univ j),grade,←tsum_mul_left]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro z
  dsimp [term]
  by_cases h:((T.roll j).leg z.val).r=0
  · simp [h]
  · rw [clear _ (Nat.pos_of_ne_zero h)];simp

end YM.Integration.WilsonOriginalTwoFlatIRFlatCopy
