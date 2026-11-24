import YM.Integration.WilsonIndependentSpoutAtomicPolar

/-! All positive angular tensors of the authorized unmarked opening agree on the
genuine cover after integrating the finite, unfitted Wilson plaquette stencil. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutInitialState
open Function Filter Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Power WilsonCoeffUV.Bank WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Prim RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open RegulatorIR.Diagram.Formal RegulatorIR.Oracle RegulatorIR.Clocks RegulatorIR.Ledger
open RegulatorIR.Binding RegulatorIR.Ward RegulatorIR.Geometry.Field
open PertExtension Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutFiniteStencil (Raw coordinates)
open WilsonIndependentSpoutMuralBoard (board)
open WilsonIndependentSpoutOrdinaryPlate (base)
open WilsonIndependentSpoutPrimitiveReport (axis)
open WilsonIndependentSpoutAtomicPolar (seats)
open scoped Classical BigOperators Topology

variable {G:Gauge}{W:Type}{M:W→ℕ}(t:Page M→Scale)(w:W)
private theorem unmixed {U:Type}(P:Pal ℝ U)(e r:ℕ): Blue.mix 1 P e r=P e r:=by
  unfold Blue.mix
  rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr (Nat.lt_succ_self e))]
  · simp
  · intro i hi ne
    have z:e-i≠0:=by have:=Finset.mem_range.mp hi;omega
    simp [PowerSeries.coeff_one,z]

theorem board_rows (bare:t (Page.opening M w)=Clocks.flat)(n:Side)(e:ℕ)(he:0<e):
    board (G:=G) t w n e=fun r x=>-topW G n e r (seats n∘x):=by
  let P:=topW G n e
  have bound r (hr:e+2<r):P r=0:=shell_lop (sprig_count _ _) e r (by omega)
  have pure:Pure P:=by
    intro r σ x
    by_cases z:r=0
    · simp [P,topW,lop,z]
    · simpa only [P,topW,lop,if_neg z] using sprig_pure (eWilson (G:=G) (c:=n)) W_green 2 e r σ x
  apply guessed (k:=e+2)
  · intro r h
    by_contra! hr
    apply h
    funext z
    have zero (p:Face ℤ):Circuit.mural G t w p e r=0:=Classical.not_not.mp fun h=>
      (not_le.mpr hr) ((Circuit.serene G t w p).scope_ e r h)
    simp only [WilsonIndependentSpoutMuralBoard.board,zero,Stalk.collect,Pi.zero_apply,tsum_zero,Finset.sum_const_zero,Finset.sum_apply]
  · intro r h
    by_contra! hr
    apply h
    funext z
    simp only [show topW G n e r=0 from bound r hr,Pi.zero_apply,neg_zero]
  · intro r σ z;unfold WilsonIndependentSpoutMuralBoard.board
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun p _=>WilsonIndependentSpoutAtomicPolar.symmetric _ ((Circuit.serene G t w (base p)).smooth e r) σ z
  · intro r σ x;exact congrArg Neg.neg (pure r σ (seats n∘x))
  · intro x
    obtain ⟨y,rfl⟩:=WilsonIndependentSpoutAtomicPolar.all n x
    rw [WilsonIndependentSpoutMuralBoard.finite t w bare n e he]
    have hv:FiniteGen P:=⟨e+2+1,fun i hi=>bound i (by omega)⟩
    have neg :totalR (-P) = -totalR P:=by simpa only [neg_one_smul] using visible_μ hv (-1)
    have bi r (hr:e+2<r):(-P) r=0:=by rw [Pi.neg_apply,bound r hr,neg_zero]
    have held:=WilsonIndependentSpoutAtomicPolar.held (seats n) (-P) (e+2) bi y
    rw [neg,map_neg] at held
    exact held.symm

theorem original (bare:t (Page.opening M w)=Clocks.flat)(A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)
    (ratio:LocalRatio Ñ)(N e r:ℕ)(he:0<e)(hr:0<r)(q:Tuple (Foot G) r):
    Circuit.padV G t w e r q=WilsonIndependentSpoutReportedQuiet.port A Ñ N N 1 e r q:=by
  have one:=WilsonIndependentSpoutMuralBoard.original (G:=G) t w e r q
  have two:=WilsonIndependentSpoutReportedQuiet.positive A Ñ simple ratio N N le_rfl 1 e r hr q
  have left:Tendsto (fun n=>WilsonIndependentSpoutMuralBoard.board t w n e r (coordinates n∘q)) atTop (𝓝 (Circuit.padV G t w e r q)):=by
    apply tendsto_const_nhds.congr'
    filter_upwards [one] with n h;exact h.symm
  apply tendsto_nhds_unique left
  apply two.congr (fun n=>?_);rw [board_rows t w bare n e he]
  unfold WilsonIndependentSpoutReportedQuiet.exposed WilsonIndependentSpoutReportedQuiet.finite
  rw [if_neg (Nat.ne_of_gt he),story_top,unmixed]
  rfl

end YM.Integration.WilsonIndependentSpoutInitialState
