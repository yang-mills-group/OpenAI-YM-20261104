import YM.Integration.WilsonVacuumPreResetPrunedBirthSites
import YM.Integration.WilsonVacuumPreResetPrunedRack
import YM.Extension.UV.Canon.Core

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedBirth
open Function Filter Set Lattice RG RG.Supply RG.Shoot Pressure Pressure.Stores Pressure.Tube
open Wilson Input Precision Next.Scheduling WilsonStartup WilsonStartup.Start
open Ovens Ovens.Pipes Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat Legato RG01Estimate
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Org
open WilsonVacuumPreResetPrunedBirthSites
open scoped Classical BigOperators

variable {G:Gauge}

theorem prepared {a:Levels G}{N:ℕ} (h:Start.Allows a N)(f:Side)(β:ℝ)(hb:β∈band a N):
    Ingredients (dictionary G f) (payload (a.params N).clip (a.budget N) G f β)
      (a.budget N) (a.clock.allowance N) (a.clock.forcedAllowance N):=by
  obtain ⟨s,k,g,loan,receipt⟩:=h.receipt
  refine ⟨k,Real.exp g-1,Real.exp g-1, digests h.clip h.radius loan hb.1 ?_,
    loan.buys h.clip hb.1,receipt⟩
  refine le_trans ?_ h.income
  unfold Start.book overhead
  have pos:=item_pos G (a.budget N)
  have cap:‖β‖≤2*a.clock.hatBeta N:=by rw [Real.norm_of_nonneg (loan.slope.trans hb.1)];exact hb.2
  gcongr

variable (R:Run G)(archive:Extension.UV.Archive R.alloy.B)(m:ℕ)
   {c f:Side}(H:f.val=c.val*(R.alloy.B.a.S.block m).val)(β:ℝ)
   (hb:β∈band R.alloy.B.a (m+1))

def paid (d:ℕ)(hd:3≤d):Board.Insured R.alloy (m+1) m d H β Shapes where
   rep:=filed f (R.alloy.B.kin.path (m+1) (m+1)) (R.alloy.B.a.params (m+1)).clip
     (R.alloy.B.a.budget (m+1)) β
   pathU:=rfl
   clip:=rfl
   β':=rfl
   point:=rfl
   legal:=(prepared (archive.startup (m+1)) f β hb).gates _ _ β 0
   sacrifice:=(Set.range (roster G f))ᶜ
   music:=roster G f
   coverage:=by simp [Evoc.Record]
   cost:=by
     obtain ⟨member,holes⟩:=mask (R.alloy.B.kin.path (m+1) (m+1)) (R.alloy.B.a.params (m+1)).clip
       (R.alloy.B.a.budget (m+1)) β (Pane.panel R.alloy m H)
     exact ⟨member,fun i z hz=>(holes i z hz).trans hd⟩

theorem measured (d:ℕ)(hd:3≤d)(U:Config G f):
    (paid R archive m H β hb d hd).rep.eval U=bare β U:=by
  have match₀:=(prepared (archive.startup (m+1)) f β hb).unshifted
    (R.alloy.B.kin.path (m+1) (m+1)) (R.alloy.B.a.params (m+1)).clip β 0 U
  rw [show (paid R archive m H β hb d hd).rep.eval U=_ from match₀]
  rw [archive.top]
  simp only [payload,Pi.zero_apply,tsum_zero,Real.exp_zero,mul_one]
  exact evaluates (archive.startup (m+1)).clip U

theorem zero_debt (d:ℕ)(hd:3≤d):let A:=paid R archive m H β hb d hd
    Inherit.Debits A.rep A.sacrifice 0:=
  debit _ _ _ β

end YM.Integration.WilsonVacuumPreResetPrunedBirth
