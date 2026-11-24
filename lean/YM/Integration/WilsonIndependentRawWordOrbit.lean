import YM.Integration.WilsonIndependentRawWordTransport
import YM.RegulatorIR.Centered.Breadth

/-! Numerical comparison of the entire submitted observable on its finite
Wilson orbit board with the scalar of its stopped cover recursion. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentRawWordOrbit
open RegulatorIR Lattice RegulatorIR.Geometry RegulatorIR.Binding
open RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Uniform WilsonIndependentRawWordTransport
open scoped ENNReal

variable {G:Gauge}{W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G}{R:Reel S}
  {T:S.Accounts}{Γ:Flap M→Layer (Foot G) (Foot G)}{V:Flap M→Bride G}
  {L:Meter W}{c:Flap M→ℝ≥0∞}{p b u m s e:ℕ}{D J:Choice M}{c₀ γ:ℝ}{x:W→Room}
  (A:Cylinder R T Γ V L c p b u)(Z:T.Report m)(U:W→Portrait G)
  (H:∀ w,BasisT m s (U w) (Z.main (Page.opening M w)))
  (ticket:Lantern S D L c γ)
  (seed:Opening (p:=p) (x:=x) (u:=u+b+b) (L:=L) Z (wage:=1))
  (clear:0<c₀)(center:S.cushion c₀ x)(terminal:R.Endings L)
include A H ticket seed clear center terminal

theorem original (he:e≤p)(older:D.age≤J.age) :
    Carry L (fun w=>ENNReal.ofReal (S.modifyErr 0 b γ J w))
      (fun w=>‖plotPT (R.clock (Page.opening M w)) (vital (TopF n w) (U w)) s e
        -note (Z.main (J.choose w) e 0)‖ₑ) := by
  have half := A.leads ticket
  have hk:14≤quantum b u:=by have h:=A.positive; unfold quantum; omega
  have ward := A.rates.preWard A.inspiration T Z U A.bulk A.price hk A.port H
  have funded := WilsonIndependentRawWordTransport.early Z A.creators A.bulk half.lead
    (by unfold quantum; omega) seed (fun _=>ENNReal.one_ne_top) ward D
  exact A.transmission Z U H ticket funded clear center he older terminal

theorem numerical (he:e≤p)(older:D.age≤J.age) :
    ∃ C:ℝ, ∃ k:ℕ, 0≤C ∧ ∀ w,
      ‖plotPT (R.clock (Page.opening M w)) (vital (TopF n w) (U w)) s e
        -note (Z.main (J.choose w) e 0)‖ ≤
        C*(L.val w).toReal^k*S.modifyErr 0 b γ J w := by
  apply Centered.Carry_rt _ (original A Z U H ticket seed clear center terminal he older)
  intro w
  exact add_nonneg (S.transfer_pos _).le (inv_nonneg.mpr (Real.rpow_nonneg (S.hl _).le _))

end YM.Integration.WilsonIndependentRawWordOrbit
