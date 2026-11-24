import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonMarkedIndependentFoldedBirth
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildScalarSlot
open Filter Function Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Embroider.Canvas
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d:ℕ}
abbrev grade:Unit→ℕ:=fun _=>0

private def probe:Scroll 0:=⟨fun _=>1,(show ContDiff ℝ (↑(0:ℕ)) (fun _:E=>(1:ℝ)) from contDiff_const)⟩
private def angle:Knob 0:=⟨0,Fin.elim0⟩
private def point:Vote 0:=
  (show Volume 0→ₗ[ℝ]ℝ from
    {toFun:=fun f=>f.val angle zeroC,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}).mkContinuous 1
    (fun f=>by change ‖f.val angle zeroC‖≤1*‖f‖; rw [one_mul];exact registry f angle zeroC)

def inlet:ℝ→L[ℝ]Pen grade {()}:=(ContinuousLinearMap.id ℝ ℝ).smulRight (petal grade () point)
def outlet:Pen grade {()}→L[ℝ]ℝ:=touch (fun _:Unit=>page 0 probe) {()}

theorem submitted(t:ℝ):outlet (inlet t)=t:=by
  change touch _ {()} (t • petal grade () point)=t
  rw [map_smul,petal_hit]
  change t*(write 0 probe angle zeroC)=t
  rw [draft]
  change t*(iteratedFDeriv ℝ 0 probe.val zeroC.val _)=t
  rw [iteratedFDeriv_zero_apply]
  exact mul_one t

def roster (X:Era G ℝ)(J:Finset Unit):Era G (Pen grade J):=
  if h:J={()} then h.symm ▸ tuftV inlet X else 0

theorem empty(X:Era G ℝ):roster X ∅=0:=by simp [roster]

theorem full(X:Era G ℝ):roster X {()}=tuftV inlet X:=by simp [roster]

theorem legal {X:Era G ℝ}(h:Auth d X):Eu (fun _:Unit=>d) (roster X):=by
  intro J
  by_cases s:J={()}
  · subst J
    simpa only [full,mass,Finset.sum_singleton] using h.tuft inlet
  · simpa only [roster,dif_neg s] using (unstamped (G:=G) (k':=mass (fun _:Unit=>d) J) (V:=Pen grade J))

/-- The marked local salary is charged before testing. At zero angular
degree the original charged coordinate stays in the occupied entry. -/
theorem paid {X:Era G ℝ}{e:ℕ}{s A:ℝ}(hp:0≤A)
    (h:∀i≤e,∀r,Wig terrain (fun _:Unit=>0) s A {()} (X.2 i r)):
    safeB (fun _:Unit=>0) (roster X) {()} e s (‖inlet‖*A):=by
  intro J _ i hi r
  by_cases hj:J={⟨⟩}
  · subst J
    rw [full,Finset.card_singleton,pow_one]
    refine ⟨mul_nonneg (norm_nonneg inlet) hp,?_⟩
    intro z
    change ‖inlet (X.2 i r z)‖≤_
    exact (inlet.le_opNorm _).trans ((mul_le_mul_of_nonneg_left ((h i hi r).2 z) (norm_nonneg inlet)).trans_eq
      (by ring))
  · rw [roster,dif_neg hj]
    exact Wig.zero.more (pow_nonneg (mul_nonneg (norm_nonneg inlet) hp) _)

end YM.Integration.WilsonPointChildScalarSlot
