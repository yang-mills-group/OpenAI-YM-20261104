import YM.Integration.WilsonSeparatedOriginalSlabWatchContrast
import YM.RG05Readout.Petals.Bullet

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchGauge
open Function Filter Set MeasureTheory Wilson Lattice RG Source RG05Readout Native Address Flatten Pulse
open RG17 Extraction Extra.Histories
open Next.UVStress Spec OPE OPE.Orbits WilsonSeparatedOriginalSlabWatchContrast
open scoped BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}
variable {I:Type}[Fintype I][DecidableEq I]{b N p:ℕ}

theorem key (H:C.Makes){d:ℕ}(x:Palette C d)(a:Mark C d)(y:Site (C.side N p)):GaugeInvariant (Pulse.key C N p d x a y):=by
  rw [Petals.pulses_key a H y x];intro τ U
  simpa only [Pi.smul_apply] using congrArg (fun z:ℂ=>(C.S.a N:ℂ)^(kept a.1) • z) (C.invariant H N p _ _ _ τ U)

theorem joint (H:C.Makes)(s:I→ℕ)(v:(i:I)→Palette C (s i))(y:I→Site (C.side N p))(Ψ:Wave I):GaugeInvariant (Pulse.harpoon s v y Ψ):=by
  intro τ U;change (∑a:(i:I)→Mark C (s i),_) = _
  apply Finset.sum_congr rfl;intro a _;apply congrArg (_*·)
  exact Finset.prod_congr rfl fun i _=>key H (v i) (a i) (y i) τ U

theorem physical (H:C.Makes)(s:I→ℕ)(v:(i:I)→Palette C (s i))(top:b≤N)(r:ℝ)(Ψ:Wave I)(m:ℕ)(g:Body):
    GaugeInvariant (constellation (C:=C) (p:=p) s v r Ψ top m g):=by
  intro τ U;unfold constellation;simp only [Pi.smul_apply,Finset.sum_apply]
  apply congrArg (_ • ·);apply Finset.sum_congr rfl;intro o _;unfold meet
  apply MeasureTheory.integral_congr_ae;filter_upwards with z;apply congrArg (_*·)
  unfold Pulse.scalp;simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,LinearMap.comp_apply]
  apply Finset.sum_congr rfl;intro t _;exact congrArg (_ • ·) (joint H s v _ _ τ U)

theorem filed (H:C.Makes)(L:Layout F)(s:I→ℕ)(r:ℝ)(w:(i:I)→C.label (s i))(Y:(p:ℕ×ℕ)→(i:I)→Emblems C (s i))
    (k m:ℕ)(Ψ:Wave I)(g:Body)(p:ℕ×ℕ):GaugeInvariant (full L s r w Y k m Ψ g p):=by
  unfold full;split
  · exact physical H s _ _ r Ψ m g
  · exact fun _ _=>rfl

end YM.Integration.WilsonSeparatedOriginalSlabWatchGauge
