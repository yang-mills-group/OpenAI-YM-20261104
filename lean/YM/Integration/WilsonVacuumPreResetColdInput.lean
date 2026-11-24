import YM.Integration.WilsonVacuumPreResetStation
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Rooms

/-! The complete measured regular catalogue in the original all-quiet incoming
sector. The rejected compact fields keep their original signed hard gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetColdInput
open Function Filter Set Finset Lattice Wilson RG RG.Shoot
open PhysicalNext PhysicalNext.Repeat Legato
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}

def rows (A:Activities G n):Activities G n:=
  {A with forced:=(Pane.pale n G).forced,K:=(Pane.pale n G).K}

theorem valid {A:Activities G n}{B:BudgetPoint}{e k:ℝ}(h:A.Valid B e k):
    (rows A).Valid B e 0:=by
  have p:=Pane.whey (n:=n) (G:=G) B
  refine ⟨⟨h.regular.smooth,h.regular.at_flat,h.regular.vanish⟩,
    ⟨p.forced.sym,p.forced.symtest,p.forced.meas,p.forced.meas_test,p.forced.reads,
      p.forced.reads_test,p.forced.permit⟩,?_,h.boundE,p.boundK⟩
  intro s b
  obtain ⟨e⟩:=h.moves s b
  obtain ⟨k⟩:=p.moves s b
  exact ⟨⟨e.ep,k.kp,e.reg_site,e.reg_support,k.forced_support,k.forced_inventory,k.forced_tests,e.valuesE,k.valuesK⟩⟩

def quiet (Y:Rep G n):Rep G n:={Y with activities:=rows Y.activities,v:=0}

theorem normalized (Y:Rep G n)(U:Config G n):
    Real.exp (Y.v*Fintype.card (Site n))*(quiet Y).eval U=
      if flags Y.p.threshold U=∅ then Y.eval U else 0:=by
  have gas:(rows Y.activities).gas Y.p U=if flags Y.p.threshold U=∅ then 1 else 0:=
    (Pane.pale_value Y.p U).2
  have ex:(quiet Y).exponent U=Y.exponent U-Y.v*Fintype.card (Site n):=by
    unfold Rep.exponent quiet
    change 0*(Fintype.card (Site n):ℝ)-Y.path.inChannels Y.clip Y.p Y.beta U -
        Y.activities.additive Y.p U = _;ring
  unfold Rep.eval
  rw [ex]
  change Real.exp _*(Real.exp _*(rows Y.activities).gas Y.p U)=_
  rw [gas]
  split_ifs with c
  · rw [Y.activities.gas_one Y.p c,mul_one,mul_one,←Real.exp_add];congr 1;ring
  · simp

variable (R:Run G)
abbrev tube (N per m:ℕ):=Pane.orchestra R.alloy N ((R.alloy.B.a.S.oneStep m per).exact_size)

def retained (N per m:ℕ):Rep G (R.family.side (m+1) per):=
  {Pane.virgin (tube R N per m) (R.family.path.levels.budget (m+1))
    (R.family.path.β N per (m+1)) with
    activities:=rows (R.family.path.rep N per (m+1)).activities}

theorem original {N per m:ℕ}(hm:m<N):
    let Y:=R.family.path.rep N per (m+1)
    let B:=R.family.path.levels.budget (m+1)
    (rows Y.activities).Valid B (R.family.path.levels.clock.allowance (m+1)) 0 ∧
    (rows Y.activities).K=(Pane.pale (R.family.side (m+1) per) G).K ∧
    (rows Y.activities).forced=(Pane.pale (R.family.side (m+1) per) G).forced ∧
    retained R N per m=quiet Y ∧
    ∀ U,Real.exp (Y.v*Fintype.card (Site (R.family.side (m+1) per)))*(retained R N per m).eval U =
      if flags B.threshold U=∅ then Y.eval U else 0:=by
  intro Y B
  have reg:=R.makes.wilson.represents N per (m+1) hm
  have p:Y.p=B:=reg.vac
  have live:Lives R.alloy.B.bake N (m+1) per Y:=((R.T.sticks N per).prices (m+1) (Nat.zero_le _) hm).1
  have path:Y.path=R.alloy.B.kin.path N (m+1):=by rw [live.path,R.alloy.B.bases]
  have fit:retained R N per m=quiet Y:=by
    unfold retained quiet Pane.virgin tube Pane.orchestra
    dsimp only
    congr 1 <;> first | exact path.symm | exact live.clip.symm | exact p.symm
  refine ⟨p ▸ valid reg.good.labels,rfl,rfl,fit,?_⟩
  intro U
  rw [fit,←p]
  exact normalized Y U

end YM.Integration.WilsonVacuumPreResetColdInput
