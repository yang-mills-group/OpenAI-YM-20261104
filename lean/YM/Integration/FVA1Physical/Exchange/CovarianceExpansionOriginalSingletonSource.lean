import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTestedSingleton
import YM.Next.MULTISOURCE.First
import YM.Source.Insertion

/-! Read one occupied column of the actual multi-source Gallery as the
ordinary forced coefficient of the original source representation.  The
identity preserves every other actor at its real vacuum weight and the
uncut denominator.  No source is enrolled by equality of evaluations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal Source QuadraticLocal.Fusion.Attached
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{d:ℕ}{V T I:Type}[DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

def oneSource (F:Labels.Frame G d)(t:T)(a:V):Coefficient F n where
  x:=0
  support:=fun _=>{o a}
  regular:=0
  forced:=fun i U=>(A.K.hard t i U).part (C.fire a)

theorem original_owner_source (F:Labels.Frame G d)(t:T)(a:V)(U:Config G n)(s:Finset ℕ):
    (packet P.activities P.p (A.K.hard t) U s).part (C.fire a)=
      (oneSource A F t a).marked P s U:=by
  unfold packet Coefficient.marked
  split
  · simp only [Multi.first_of_prod,A.K.quiet];rfl
  rfl

theorem original_singleton_source (F:Labels.Frame G d)(t:T)(a:V)(U:Config G n)
    {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e):
    originalRaw A t (C.fire a) U=
      (∑'s,(oneSource A F t a).marked P s U)/(P.activities.gas P.p U:ℂ):=by
  unfold originalRaw Gallery.gas
  rw [Poly.share (Hard.packet_summing A.K paid en wp t U)]
  exact congrArg (fun z:ℂ=>z/(P.activities.gas P.p U:ℂ)) (tsum_congr (original_owner_source A F t a U))

/-- Scales only the distinguished marked owner. The relation to a
separately issued source is literal at the filed forced entries and
the displayed price uses its own original denominator and unit. -/
theorem physical_singleton_in_units {F:Labels.Frame G d}(Z:Coefficient F n)(t:T)(a:V)
    (U:Config G n){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)
    (γ unit:ℂ)(nz:unit≠0)(same:∀i,(A.K.hard t i U).part (C.fire a)=γ*Z.forced i U):
    (w a:ℂ)*originalRaw A t (C.fire a) U=
      ((w a:ℂ)*γ/unit)*(unit*(∑'s,Z.marked P s U)/(P.activities.gas P.p U:ℂ)):=by
  have rows(s:Finset ℕ):(oneSource A F t a).marked P s U=γ*Z.marked P s U:=by
    unfold Coefficient.marked
    split
    · simp only [oneSource,same,Finset.mul_sum,mul_assoc]
    simp
  rw [original_singleton_source A F t a U wp paid en,show (∑'s,(oneSource A F t a).marked P s U)=
    γ*∑'s,Z.marked P s U from (tsum_congr rows).trans (tsum_mul_left ..)]
  field_simp [nz]

/-- A funded original deposited hard column in its own units supplies the
restored whole-source pointwise price, allowing arbitrary complex conversion. -/
theorem original_singleton_enrolled_cap {F:Labels.Frame G d}(Z:Coefficient F n)(t:T)(a:V)
    (U:Config G n){w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}(paid:A.K.Paid w P.p.B e κ)(en:0≤e)
    (γ unit:ℂ)(nz:unit≠0)(same:∀i,(A.K.hard t i U).part (C.fire a)=γ*Z.forced i U)
    (K:ℝ)(stock:‖unit*(∑'s,Z.marked P s U)/(P.activities.gas P.p U:ℂ)‖≤K):
    ‖(w a:ℂ)*originalRaw A t (C.fire a) U‖≤‖(w a:ℂ)*γ/unit‖*K:=by
  rw [physical_singleton_in_units A Z t a U wp paid en γ unit nz same,norm_mul]
  exact mul_le_mul_of_nonneg_left stock (norm_nonneg _)

end YM.Integration.FVA1Physical.Exchange.RoseCut
