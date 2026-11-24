import YM.Integration.WilsonOriginalRelativeMixedFields
import YM.Integration.WilsonOriginalNamedRelativeRows

/-! Regularity on the full held chart and the actual paid field at each set of root labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPaidMixedRegularity
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonEmittedRootedJetWage WilsonOriginalMixedCoveredRead
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (p:Fin (Pages n N)) (which:ι→Prop)

theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ):
    ContDiff ℝ ω (field h M t p which):=by
  let ink:=fun i=>(M i).paint t
  let crew:=fun i=>TwoReset.copy h (M i) p
  have U:=copy_staff h M grades ink (Air.license M ink grades w stock hs (fun i=>stock.honor i t)) p
  let profile:=fun z:Joint G N=>RG.increment 1 z.2
  have heard:(fun z:Joint G N=>Air.sums crew ink which z.1 (profile z))=field h M t p which:=by
    funext z
    simp only [field,Air.sums,ScatterR.familyAt,WilsonOriginalPaidWalkCover.letter,crew,ink,profile]
  rw [←heard,contDiff_iff_contDiffAt]
  intro y
  have identified (z:Joint G N):profile z=Stationary.input G N (edgeColor.symm z.2):=by
    funext e
    rw [input_color,ContinuousLinearEquiv.apply_symm_apply]
    change G.lieExp (z.2 e)*1=G.lieExp (z.2 e)
    rw [mul_one]
  have fit (e:Edge (Site N)):ContDiffAt ℝ ω (fun z:Joint G N=>G.mat (profile z e)) y:=by
    simp_rw [identified]
    let L:=(Stationary.arm G N 1).toContinuousLinearMap ∘L ((edgeColor.symm.toContinuousLinearMap) ∘L (ContinuousLinearMap.snd ℝ ℝ (Directions G N)))
    exact (Work.F03.represent_smooth (G:=G) e).contDiffAt.comp (f:=L) y L.contDiff.contDiffAt
  exact (Air.rings crew ink grades U which Prod.fst profile y contDiffAt_fst fit 0 Fin.elim0).1

theorem suspended {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j:ℕ):
    ContDiff ℝ ω (fun z:Joint G N=>(z.1^j:ℝ) • field h M t p which z):=
  (contDiff_fst.pow j).smul (original h M t p which stock hs)

end YM.Integration.WilsonOriginalPaidMixedRegularity
