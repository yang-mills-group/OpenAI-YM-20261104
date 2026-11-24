import YM.Integration.WilsonIndependentSpoutSchurVacuum
import YM.Integration.WilsonIndependentSpoutChronologicalClock
import YM.Integration.WilsonIndependentConditionalOrdinaryCover

/-! The nonlinear unmarked finite history and its actual two adjacent
reporting clocks on each ordinary Wilson board. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutSchurStory
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Power
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior Next.Free
open WilsonIndependentConditionalPositiveVacuum (value)
open scoped Classical BigOperators MatrixOrder

private theorem cut {U:Type}[Fintype U]{P:Pal ℝ U}{d:ℕ}(hp:shellK d P)
    (α:Cost)(e:ℕ)(b:Lawn U):
    value (redo α (flash P)) e b=value (redo α (flash (lop P))) e b:=by
  let w:Cost:=PowerSeries.mk fun i=>P i 0 (fun j=>j.elim0)
  have split:flash P=flash (lop P)+soil w:=by
    conv_lhs=>rw [lop_pres P]
    rw [flash_add (finite_shell (shell_lop hp)) (finite_shell (uband_length _ _ d)),uband_flash]
  rw [split,map_add,WilsonIndependentSpoutThermalLog.cash]
  simp only [value,soil,map_add,coeff_map,MvPolynomial.eval_C]
  ring

theorem original {G:Gauge}(A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)
    {N m:ℕ}(finer:m<N)(c:Side)(e:ℕ)(b:TreeVars G c):
    let L:=loose A m;let S:=mStep A c m;let F:=repeatF S
    let H:=freeForms A N (m+1);let Y:=freeForms A N m;let Q:=roam A N m c
    let V:=(story A Ñ N (m+1)).1 (c*L.L)
    let α:=relativeC A Ñ N (m+1) (N-(m+1))
    let α':=relativeC A Ñ N m (N-m)
    value (logOf (WilsonIndependentSpoutSchurVacuum.read S F H Y Q α Ñ V)) e b=
      value (orbC (precisionC G c Y)) e b-value (redo α' (flash ((story A Ñ N m).1 c))) e b:=by
  intro L S F H Y Q V α α'
  have funded:Interlace H V:=(old A Ñ simple ratio N (m+1) finer).basis (c*L.L)
  have gate:=horizon_step A m N finer c (c*L.L) rfl
  have clock:constantCoeff α=1:=angularC simple ratio (by omega)
  have visit:(story A Ñ N m).1 c=mix (ratioHigh A Ñ N m) (lop (winter S F H Y Q Ñ V)):=by
    rw [story_stride A Ñ finer];rfl
  have order:=winter_band S F H Y Q ratio funded.lamp
  have reset:redo α' (redo (ratioHigh A Ñ N m) (flash (lop (winter S F H Y Q Ñ V))))=
      redo α (flash (lop (winter S F H Y Q Ñ V))):=by
    unfold α'
    rw [show N-m=1+(N-(m+1)) by omega]
    exact WilsonIndependentSpoutChronologicalClock.original A Ñ simple ratio (by omega) _
  rw [WilsonIndependentSpoutSchurVacuum.held S F H Y Q α clock funded.lamp funded.stem
    (A.blocks m 0).branches gate (age_sym A ..) ratio (Convention.tree_pos A m N rfl) funded.shape,
    visit,←redo_stern _ (shell_lop order),reset,←redo_stern α order,cut order]

end YM.Integration.WilsonIndependentSpoutSchurStory
