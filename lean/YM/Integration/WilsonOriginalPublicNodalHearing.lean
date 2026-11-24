import YM.Integration.WilsonOriginalPublicNodalFiling
import YM.Integration.WilsonOriginalTwoFlatPublicSameField
import YM.Integration.WilsonOriginalMicroscopicGuardedHeld
import YM.Integration.WilsonSeparatedOriginalSlabHeldProxy

/-! An original unconditioned cutoff word and an independently normalized finite
board, tested at the same occupied positions. The joint physical entry and the
registered group responses are retained as signed quantities. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonOriginalPublicNodalHearing
open Finset MeasureTheory Lattice Wilson RG Source Labels PowerSeries
open RegulatorIR.FVAAlt2 Pert.Asymptotics Extra.Histories PhysicalNext PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalMicroscopicGuardedTrial
open WilsonOriginalPublicTrialInput WilsonOriginalPublicTrialFigure
open WilsonOriginalPublicPivotReflected (evaluated board)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOriginalPublicNodalFiling (residual)
open OPE.Therm Push.AbsoluteSums.Animals MergeProof.Accent
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per K u f:ℕ}
local notation "C" => R.family
local notation "X" k:max => Config G ((C).side k per)
local notation "read" => actualTransport (C) (N:=N) (p:=per)

theorem phase (un:u≤N)(Y:(X N→ℂ)):
    (C).omega N per Y-read Y un 1=WilsonOriginalTwoFlatGridScaling.gap R N per u un Y:=by
  unfold WilsonOriginalTwoFlatGridScaling.gap WilsonThermometerUnitFilingCoarse.reading
  rw [gust_base,←WilsonSeparatedOriginalSlabHeldProxy.normalized R un Y]
  ring

theorem guard (kn:K≤N)(uk:u≤K)(o:Fin 3→Site ((C).side K per))(v:∀a,(C).label (d a))
    (s:Finset (Fin 3))(U:X u):
    read (face (raw R d N per K o v) s) uk U-read (face (guarded R d N per K o v) s) uk U=
      read (gap R d N per K o v s) uk U:=by
  have bank:=unary R d N per K o v
  have income (F:Fin 3→X K→ℂ)(meas:∀a,Measurable (F a))
      (bill:∀a V,‖F a V‖≤cap R d N per K v a):Envelope (face F s):=by
    refine ⟨Finset.measurable_prod s (fun a _=>meas a),∏a∈s,cap R d N per K v a,?_⟩
    intro V
    change ‖∏a∈s,F a V‖≤_
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>bill a V)
  have h:=ActualWilsonAbsoluteTransport.sub (C) R.makes kn
    (ActualWilsonAbsoluteTransport.weighted (C) R.makes kn
      (income _ (fun a=>(bank a).2.1) (fun a V=>((bank a).2.2 V).2)))
    (ActualWilsonAbsoluteTransport.weighted (C) R.makes kn
      (income _ (fun a=>(bank a).1) (fun a V=>((bank a).2.2 V).1))) uk
  exact (congrFun h U).symm

def born (Y:∀a:Fin 3,ℕ×ℕ→(C).label (d a))(fn₀:f≤N)(roots:Fin 3→ Cover)(s:Finset (Fin 3)):(X N→ℂ):=
  WilsonOriginalTwoFlatGridCapture.word R (fun a:s=>d a) f N per fn₀ (fun a=>roots a)
    (fun a=>Y a (N,per))

def swap (Y:(X N→ℂ))(kn:K≤N)(uk:u≤K)(o:Fin 3→Site ((C).side K per))
    (v:∀a,(C).label (d a))(s:Finset (Fin 3))(U:X u):ℂ:=
  read Y (uk.trans kn) U-read (face (guarded R d N per K o v) s) uk U

def filed (W:Initialize G)(x:Sample 3)(v:∀a,(C).label (d a))(s:Finset (Fin 3))
    (uk:u≤K)(U:X u)(q:ℕ)(g:ℝ):ℂ:=
  ∑b:Columns R (fun a:s=>d a),weight R (fun a:s=>d a) g (fun a=>v a) b*
    residual R (fun a:s=>d a) (fun a=>x.layout a) x.F.p (W.tree x.F.p) (N:=N) uk U b q g

variable (j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))(before:∀a,j a≤K)(registered:Indexed R d j target η M Y)
    (live:K<N)(fk:f≤K)(uk:u≤K)(s:Finset (Fin 3))(roots:Fin 3→ Cover)
    (o:Fin 3→Site (R.family.side K per))(W:Initialize G)(x:Sample 3)
    (lift:∀a:s,wrap (R.family.side K per) (x.layout a)=o a)(q:ℕ)
local notation "g₀" => regulatorRun (C) N per K
local notation "v₀" => vector R d j K target η M Y before registered N per
local notation "vₖ" => fitted R d j K target η M Y before registered N per
local notation "Fₙ" => born R d (per:=per) Y (fk.trans live.le) roots s

include lift in
theorem original (warm:g₀≠0):
    (C).omega N per Fₙ-evaluated q g₀ (board R W d v₀ x s)-
      swap R d Fₙ live.le uk o vₖ s 1-filed R d W x v₀ s (N:=N) (per:=per) uk 1 q g₀=
    WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans live.le) Fₙ-
      read (gap R d N per K o vₖ s) uk 1:=by
  have h:=WilsonOriginalPublicNodalFiling.original R (fun a:s=>x.layout a) x.F.p (W.tree x.F.p)
    d j target η M Y before registered live uk 1 Subtype.val o lift q warm
  have shape:(fun V:X K=>∏a:s,raw R d N per K o vₖ a V)=face (raw R d N per K o vₖ) s:=by
    funext V
    exact Finset.prod_coe_sort s (fun a=>raw R d N per K o vₖ a V)
  change read (fun V=>∏a:s,raw R d N per K o vₖ a V) uk 1-
    evaluated q g₀ (board R W d v₀ x s)=filed R d W x v₀ s (N:=N) (per:=per) uk 1 q g₀ at h
  rw [shape] at h
  unfold swap
  rw [←phase R (uk.trans live.le) Fₙ]
  linear_combination h-guard R d live.le uk o vₖ s 1

include lift in
theorem charged (warm:g₀≠0)(prior:u+1≤K){A:ℝ}
    (physical:‖WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans live.le) Fₙ‖≤A):
    ‖(C).omega N per Fₙ-evaluated q g₀ (board R W d v₀ x s)-
      swap R d Fₙ live.le uk o vₖ s 1-filed R d W x v₀ s (N:=N) (per:=per) uk 1 q g₀‖≤
    A+WilsonOriginalMicroscopicGuardedPosterior.gross R d N per K vₖ s*
      (WilsonMacroscopicRichFlatPosteriorLaw.law R N per prior 1).real
        (SelectedCofactorAnchoredRegister.hot (G:=G) ((C).path.rep N per K).p.threshold
          (footprint R d per K o s)):=by
  rw [original R d j target η M Y before registered live fk uk s roots o W x lift q warm]
  exact (norm_sub_le ..).trans (add_le_add physical
    (WilsonOriginalMicroscopicGuardedHeld.original R d live.le prior o vₖ s 1).2)

end YM.Integration.WilsonOriginalPublicNodalHearing
end
