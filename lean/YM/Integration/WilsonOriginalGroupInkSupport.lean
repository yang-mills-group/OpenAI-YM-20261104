import YM.Integration.WilsonOriginalGroupInkDirections
import YM.Next.RANK.Bordering

/-! The finite Wilson word reads its two endpoints only within its filed footprint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGroupInkSupport
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry Exterior Stationary
open PertExtension.Series WilsonOriginalGroupInkDirections WilsonOriginalLinkedAngularPage
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def keep (G:Gauge) {n:Side} (s:Finset (Site n)) : Link G n→L[ℝ]Link G n :=
  LinearMap.toContinuousLinearMap {
    toFun:=fun a y=>if y.1∈s then a y else 0
    map_add':=by intro a b;funext y;by_cases h:y.1∈s <;> simp [h]
    map_smul':=by intro t a;funext y;by_cases h:y.1∈s <;> simp [h] }

theorem field {k:ℕ} (m:Atom G k) (x:Site n) :
    Helmet.frame m x = Helmet.frame m x ∘ keep G (m.footprint x) := by
  funext a
  apply Next.Rank.Alarm.unmasked_space
  intro e here _
  change G.lieExp _ * _ = G.lieExp _ * _
  congr 2
  ext i
  change a (e.1,coord e.2,i)=(if e.1∈m.footprint x then a (e.1,coord e.2,i) else 0)
  exact (if_pos here).symm

theorem receipt (T:Row o J G X) (j:ℕ) :
    T.markReceipt j=T.markReceipt j ∘ keep G (T.atom.footprint T.center) := by
  let m:=T.atom
  let x:=T.center
  let Q:=keep G (m.footprint x)
  funext a
  change (if _ then Radial.jet (Helmet.frame m x) (band T j) a else 0)=
    if _ then Radial.jet (Helmet.frame m x) (band T j) (Q a) else 0
  split_ifs
  · calc
      _ = Radial.jet (Helmet.frame m x ∘ Q) (band T j) a :=
        congrArg (fun f=>Radial.jet f (band T j) a) (field m x)
      _ = _:=by
        unfold Radial.jet
        rw [Next.Foundations.jets_linear Q ((Helmet.frameGrade m x).smooth.of_le le_top)]
        rfl
  · rfl

theorem away (T:Row o J G X) (t:X) (j r:ℕ) (x:Fin r→Site n×Loc G 1)
    (i:Fin r) (missing:(x i).1∉T.atom.footprint T.center) :
    coefficient r (jet T t j) x=0 := by
  let Q:=keep G (T.atom.footprint T.center)
  let F:=jet T t j
  have eq:F=F ∘ Q:=by
    funext a
    exact congrArg (fun y:ℝ=>T.paint t*(y:ℝ)) (congrFun (receipt T j) a)
  have smooth:ContDiff ℝ r F:=by
    let L:ℝ→L[ℝ]ℂ:=(ContinuousLinearMap.id ℝ ℝ).smulRight (T.paint t)
    have repr:F=L ∘ T.markReceipt j:=by
      funext a
      change T.paint t*_=(T.markReceipt j a:ℝ) • (T.paint t)
      rw [Complex.real_smul];ring
    rw [repr]
    exact L.contDiff.comp (WilsonMarkedAngularTestInvoice.regular (rank T j (band T j) le_rfl) r)
  have zero:Q (ray G (x i))=0:=by
    funext y
    change (if y.1∈T.atom.footprint T.center then (if y=x i then (1:ℝ) else 0) else 0)=0
    by_cases z:y=x i
    · subst y;simp [missing]
    · simp [z]
  change iteratedFDeriv ℝ r F 0 (fun h=>ray G (x h))=0
  conv_lhs => rw [eq]
  rw [Q.iteratedFDeriv_comp_right smooth 0 le_rfl,map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact (iteratedFDeriv ℝ r F 0).map_coord_zero i zero

end YM.Integration.WilsonOriginalGroupInkSupport
