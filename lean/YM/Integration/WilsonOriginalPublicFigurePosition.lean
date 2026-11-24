import YM.Integration.WilsonOriginalPublicFigureRoster
import YM.Integration.WilsonMaxwellThermometerChargedHeads
import YM.Integration.WilsonMaxwellThermometerPositionCurrency
import YM.XSpace.KPos

/-! The physical input in a jointly fitted finite position frame, after the
published kinetic substitution. The same inverse acts on every occupied face. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 450000
namespace YM.Integration.WilsonOriginalPublicFigurePosition
open Finset Filter Function Lattice Wilson RG PhysicalNext.Repeat.Legato PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 XSpace.Expense Maxwell Maxwell.Wick
open MS MS.Book MS.Book.Program OPE RegulatorIR.FVAAlt2
open scoped Classical BigOperators Topology
variable {G:Gauge}{d n:ℕ}
def clock (team:ℕ→Plan)(θ:ℝ)(R:Reports G d):Reports G d:=
  fun q=>∑i∈Finset.Iic q,Program.cut (Program.shift team θ) i q • R i

theorem clock_ground (team:ℕ→Plan)(θ:ℝ)(R:Reports G d):clock team θ R 0=R 0:=by
  rw [clock,show Finset.Iic (0:ℕ)={0} from by ext; simp,Finset.sum_singleton]
  simp [Program.cut]

theorem clock_read (team:ℕ→Plan)(θ:ℝ)(R:Reports G d)(φ:Test n)(p:Fin n→Sec G d):
    said (clock team θ R) φ p=YM.FVAAlt2.Lobby.redo team θ (said R φ p):=by
  ext q
  rw [said,PowerSeries.coeff_mk]
  unfold YM.FVAAlt2.Lobby.redo
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [PowerSeries.coeff_mk,Program.rules]
  simp only [clock,YM.FVAAlt2.Ends.unpack,said,PowerSeries.coeff_mk,Finset.sum_apply,
    LinearMap.sum_apply,_root_.sum_apply,Pi.smul_apply,LinearMap.smul_apply,_root_.smul_apply]

def booked (V:Store G)(W:Initialize G)(m:Mesh)(d:ℕ)(team:ℕ→Plan)(θ:ℝ):Reports G d:=
  (V.survey d).fit (V.prepared d) (clock team θ (batch W m d))

theorem original (V:Store G)(W:Initialize G)(d:ℕ):
    ∀ᶠ m in Front,∀(team:ℕ→Plan)(θ:ℝ),
    let raw:=clock team θ (batch W m d)
    let Z:=Normalize.deck ((V.survey d).Lays (V.prepared d) raw)
    ∃B:Guard G d,Formal B ∧ Z*B=1 ∧ B*Z=1 ∧
      (∀q,coeff q B (leaf G d)=if q=0 then leaf G d else 0) ∧
      (∀U:Guard G d,Formal U → constantCoeff U=1 →
        booked V W m d team θ=(V.survey d).fit (V.prepared d) (realm U raw)) ∧
      ∀n (φ:Test n)(p:Fin n → Sec G d)(s:Finset (Fin n)),
      YM.FVAAlt2.Lobby.redo team θ (said (batch W m d) φ (missing p s))=
        ∑b:Fin n→Dime G d,said (booked V W m d team θ) φ (fun i=>dime G d (b i))*
          ∏i,tax B (missing p s i) (b i):=by
  filter_upwards [(V.nested_solution W d frontier).2] with m known
  have works:Fray.Executed (V.survey d) (V.prepared d) (batch W m d):=
    ⟨known.1.1,known.1.2.1,known.1.2.2.2.2.2⟩
  intro team θ raw Z
  have legal:Fray.Executed (V.survey d) (V.prepared d) raw:=
    Fray.no_reset (V.survey d) (V.prepared d) works (clock_ground ..).symm
  obtain ⟨B,correct,bz,zb⟩:=reversal_exists legal.1
  refine ⟨B,correct,zb,bz,?_,?_,?_⟩
  · obtain ⟨T,rfl⟩:=correct.actions
    exact prime_deck T
  · intro U formal one
    exact Fray.invariance (V.survey d) (V.prepared d) raw U formal one legal
  · intro n φ p face
    let x:=missing p face
    rw [←clock_read,←talks]
    change said raw φ x=said (realm B (realm Z raw)) φ x
    rw [parlance,zb,author]

end YM.Integration.WilsonOriginalPublicFigurePosition
end
