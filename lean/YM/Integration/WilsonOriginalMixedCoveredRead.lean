import YM.Integration.WilsonOriginalSuspendedTensor
import YM.Integration.WilsonOriginalCoherentCoveredFields
import YM.QuadraticLocal.Fk.Offer

/-! Termwise mixed derivatives of the signed, separately located, originally enrolled group roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedCoveredRead
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalSuspendedWord WilsonEmittedRootedJetWage
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (p:Fin (Pages n N)) (which:ι→Prop)

def field (z:Joint G N):ℂ:=
  ∑' i,if which i then (M i).paint t*Complex.ofReal
    (Loan.letter (row h (M i) p).lamp (row h (M i) p).atom (row h (M i) p).center z.1 (RG.increment 1 z.2)) else 0

theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (σ0:0<σ)
    (r:ℕ) (u:Fin r→Slot G N) :
    HasSum (fun i=>if which i then WilsonOriginalSuspendedFootprint.at (row h (M i) p) t 0 r u else 0)
      (iteratedFDeriv ℝ r (field h M t p which) 0 (peg G N ∘ u)):=by
  let ink:=fun i=>(M i).paint t
  let crew:=fun i=>TwoReset.copy h (M i) p
  have A:=Air.license M ink grades w stock σ0 (fun i=>stock.honor i t)
  have U:=copy_staff h M grades ink A p
  let profile:=fun z:Joint G N=>RG.increment 1 z.2
  have fit (e:Edge (Site N)):ContDiffAt ℝ ω (fun z:Joint G N=>G.mat (profile z e)) 0:=by
    have identified (z:Joint G N):profile z=Stationary.input G N (edgeColor.symm z.2):=by
      funext y
      rw [input_color,ContinuousLinearEquiv.apply_symm_apply]
      change G.lieExp (z.2 y)*1=G.lieExp (z.2 y)
      rw [mul_one]
    simp_rw [identified]
    let L:=(Stationary.arm G N 1).toContinuousLinearMap ∘L ((edgeColor.symm.toContinuousLinearMap) ∘L (ContinuousLinearMap.snd ℝ ℝ (Directions G N)))
    exact (Work.F03.represent_smooth (G:=G) e).contDiffAt.comp (f:=L) (0:Joint G N) L.contDiff.contDiffAt
  have word (i:ι): (fun z:Joint G N=>ScatterR.familyAt crew ink i z.1 (profile z)) =
      colored (row h (M i) p) t 0:=by
    funext z
    unfold colored ScatterR.familyAt
    simp only [pow_zero,one_mul]
    exact congrArg (fun b:ℝ=> ink i*(b:ℝ)) (WilsonOriginalPaidWalkCover.letter h (M i) p z.1 (profile z)).symm
  have heard:(fun z:Joint G N=>Air.sums crew ink which z.1 (profile z))=field h M t p which:=by
    funext z
    unfold Air.sums field
    apply tsum_congr
    intro i
    split_ifs with yes
    · rw [congrFun (word i) z];unfold colored;rw [pow_zero,one_mul];rfl
    · rfl
  have sound:=(Air.rings crew ink grades U which Prod.fst profile 0 contDiffAt_fst fit r (peg G N ∘ u)).2
  rw [heard] at sound
  apply sound.congr_fun
  intro i
  by_cases hi:which i
  · simp only [if_pos hi,word i]
    rfl
  · simp [hi]

end YM.Integration.WilsonOriginalMixedCoveredRead
