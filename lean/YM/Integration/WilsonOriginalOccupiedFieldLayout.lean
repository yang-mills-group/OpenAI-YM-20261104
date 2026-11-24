import YM.Integration.WilsonOriginalPaidMixedRegularity
import YM.Integration.WilsonOriginalLocatedDeckAction

/-! The signed component on its actual covered finite bank, with the full paid roster inside the sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedFieldLayout
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Poetry Stationary
open AllOrder.Floe Comparison.RG02 Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonEmittedRootedJetWage WilsonOriginalMixedCoveredRead
open WilsonOriginalRelativeMixedFields WilsonOriginalNamedRelativeRows
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G X) (t:X)
abbrev PagesOf (n N:Side):=Fin (Pages n N)

def token (i:ι) (p:PagesOf n N) (z:Joint G N):ℂ:=
  (M i).paint t*Complex.ofReal (Loan.letter (row h (M i) p).lamp (row h (M i) p).atom (row h (M i) p).center z.1 (RG.increment 1 z.2))
def frame (keep:ι→PagesOf n N→Prop) (z:Joint G N):ℂ:=
  ∑'i,∑p:PagesOf n N,if keep i p then token h M t i p z else 0
def shade (j:ℕ) (keep:ι→PagesOf n N→Prop) (z:Joint G N):ℂ:=
  (z.1^j:ℝ)*frame h M t keep z

def restricted (s:J.Mode)(u:s.val→PagesOf n N)(i:ι)(p:PagesOf n N):Prop:=
  (M i).mode=s ∧ assigned h M s.val i p=u

theorem collects {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (keep:ι→PagesOf n N→Prop)
    (p:PagesOf n N) (z:Joint G N):
    Summable (fun i=>if keep i p then token h M t i p z else 0):=by
  let ink:=fun i=>(M i).paint t
  have U:=copy_staff h M grades ink (Air.license M ink grades w stock hs (fun i=>stock.honor i t)) p
  simpa only [token,WilsonOriginalPaidWalkCover.letter,ScatterR.familyAt,ink] using
    Air.usable_all (fun i=>TwoReset.copy h (M i) p) ink grades U (RG.increment 1 z.2) z.1 (fun i=>keep i p)

theorem pages {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (keep:ι→PagesOf n N→Prop):
    frame h M t keep=∑p:PagesOf n N,field h M t p (fun i=>keep i p):=by
  funext z
  rw [Finset.sum_apply,frame,Summable.tsum_finsetSum (fun p _=>collects h M t stock hs keep p z)]
  rfl

theorem analytic {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j:ℕ)(keep:ι→PagesOf n N→Prop):
    ContDiff ℝ ω (shade h M t j keep):=by
  have smooth:ContDiff ℝ ω (frame h M t keep):=by
    rw [pages h M t stock hs keep];simp_rw [sum_fn]
    exact ContDiff.sum (fun p _=>WilsonOriginalPaidMixedRegularity.original h M t p _ stock hs)
  exact (contDiff_fst.pow j).smul smooth

theorem filed {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ)
    (L:Layout G)(T:Finset Age)(s:Hot J)(z:Joint G N):
    frame h M t (fun i _=>(M i).mode=s.val) z =
      (TwoReset.copyColor h M grades (fun i=>(M i).paint t) L T).mark s z.1 (RG.increment 1 z.2):=by
  rw [pages h M t stock hs,Finset.sum_apply]
  unfold TwoReset.copyColor
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [WilsonOriginalCoherentCoveredFields.on_page h M grades _ L T p s]
  apply tsum_congr;intro i;split_ifs <;> rfl

end YM.Integration.WilsonOriginalOccupiedFieldLayout
