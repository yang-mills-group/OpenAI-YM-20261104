import YM.FVAAlt2.Booth.Tag
import YM.RegulatorIR.Clocks.Enough
/-!
# Coherent analytic choice of RHS UnitCost for every halted era & horizon p

Uses Notebook.Scale already solved to tune repeated transport.YM.RegulatorIR.Profile. Not necessarily C.Even unless Scale.Even facts (which will hold through pre), tau positive attained locally. No horizon-uniform extension claims. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth.Ribbon
open Function Finset Set Filter MeasureTheory Lattice RG PertExtension Series Series.Radial Series.Tested
open Geometry PowerSeries Precision Binding Prim Ward Clocks Comparison.RG02 Comparison.RG02.Adjacent
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable (L: Binding.Scale) {k r:ℕ}
abbrev fees (C:UnitCost) (t:ℝ):ℝ:= ((C.rating t)^2)⁻¹
lemma ordered (C:UnitCost): ContDiffAt ℝ ω (fees C) 0:= ((C.smooth.pow 2).inv (by simp [C.origin]))
def Align (p:ℕ)(L:Binding.Scale)(T:UnitCost):= Ward.Squares p (Prim.tale L.beta) (Prim.tale (fees T))
def agenda : Adjacent.Caliber where
    measure i:= coeff i (tale L.beta)
    starts:= by rw [tale_base,L.stable]
def budgetV (r:ℕ): UnitCost:= (agenda L).direct r
lemma lives (r:ℕ): Align r L (budgetV L r):=by
    let K:=agenda L; let H:=peval (fun i=> K.measure i) r; let T:=budgetV L r
    have hv : H= K.tariff r:=by funext; rfl
    have hp : ContDiffAt ℝ ∞ H 0:= by rw [hv]; exact (K.smooth _).contDiffAt.of_le le_top
    have hu : Prim.tale (fees T)=tale H:= by apply Prim.tale_eq hp; rw [hv]; filter_upwards [K.rates r] with x hx; rw [← K.income _ x hx.le]; unfold T fees; rw [ inv_pow ]; rfl
    intro i hi; change coeff i _= coeff i (tale (fees T)); rw [hu]
    -- polynomial truncated cash. use predictsP ASP
    exact Eq.symm ((congr_fun ( ( Script.actual hp ).unique (Aspiration.polynomial _ _ )) i).trans (if_pos hi)) -- check binder
-- characterize via known Reading curve.Fork
end YM.RegulatorIR.FVAAlt2.Booth.Ribbon
