import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFiledBinSquare

/-! Transport of the actual connected OLD through one shared detector bin.
The conditional covariance of the two physical singleton readings is retained.
Both weights are the very same paid restoration weights as in the full pair.
No equality or stochastic independence of singleton fields is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators

variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

omit [Fintype V] in
def originalRaw (t:T)(s:C.Mode)(U:Config G n):ℂ:=
  (A.gas t U).part s/(P.activities.gas P.p U:ℂ)

/-- The actual pair log has both original singleton fields on exactly the same point. -/
theorem filed_pair_raw {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)
    (en:0≤e)(t:T)(U:Config G n)(live:0<P.eval U)(a b:V)(h:a≠b)(s:C.Mode)(pair:s.val={a,b}):
    (w a:ℂ)*(w b:ℂ)*filedRow A t s U = (w a:ℂ)*(w b:ℂ)*originalRaw A t s U -
    ((w a:ℂ)*originalRaw A t (C.fire a) U)*((w b:ℂ)*originalRaw A t (C.fire b) U):=by
  let ν:ℂ:=P.activities.gas P.p U
  have nz:ν≠0:=Complex.ofReal_ne_zero.mpr (pos_of_mul_pos_right live (Real.exp_nonneg _)).ne'
  have base:(A.gas t U).part C.quiet=ν:=Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid en wp t U)
  have unit:((ν⁻¹) • A.gas t U).part C.quiet=1:=by rw [Poly.part_smul,base,inv_mul_cancel₀ nz]
  change _*_*(connected (ν⁻¹ • A.gas t U)).part s=_
  rw [twins a b s (ν⁻¹ • A.gas t U) unit h pair]
  simp only [Poly.part_smul,originalRaw,div_eq_mul_inv,ν]
  ring

variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)

def binMean (B:Set Ω)(u:Ω→ℂ):ℂ:=(∫x in B,u x ∂μ)/(μ.real B:ℂ)

def binCov (B:Set Ω)(u v:Ω→ℂ):ℂ:=binMean μ B (fun x=>u x*v x)-binMean μ B u*binMean μ B v

/-- A concrete identity on the physical parcel. The term following the bracket
is its true conditional, within-measuring-bin, signed covariance, even for a
zero-mass bin. Local singleton marginal matching alone cannot drop it. -/
theorem original_pair_bin {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)
    (en:0≤e)(t:T)(π:Ω→Config G n)(live:∀x,0<P.eval (π x))
    (a b:V)(h:a≠b)(s:C.Mode)(pair:s.val={a,b})(B:Set Ω)
    (raw:IntegrableOn (fun x=>(w a:ℂ)*(w b:ℂ)*originalRaw A t s (π x)) B μ)
    (product:IntegrableOn (fun x=>((w a:ℂ)*originalRaw A t (C.fire a) (π x))*
      ((w b:ℂ)*originalRaw A t (C.fire b) (π x))) B μ):
    let X:=fun x=>(w a:ℂ)*originalRaw A t (C.fire a) (π x)
    let Y:=fun x=>(w b:ℂ)*originalRaw A t (C.fire b) (π x)
    binMean μ B (fun x=>(w a:ℂ)*(w b:ℂ)*filedRow A t s (π x))=
      (binMean μ B (fun x=>(w a:ℂ)*(w b:ℂ)*originalRaw A t s (π x))-
        binMean μ B X*binMean μ B Y)-binCov μ B X Y:=by
  intro X Y
  have eq:(fun x=>(w a:ℂ)*(w b:ℂ)*filedRow A t s (π x)) =
    fun x=>(w a:ℂ)*(w b:ℂ)*originalRaw A t s (π x)-X x*Y x:=
      funext fun x=>filed_pair_raw A wp paid en t (π x) (live x) a b h s pair
  rw [eq]
  unfold binCov binMean
  rw [integral_sub raw product]
  ring

end YM.Integration.FVA1Physical.Exchange.RoseCut
