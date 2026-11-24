import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionOriginalSingletonSource
import YM.Extra.SOURCE_HISTORIES.Unit

/-! The literal singleton read from the complete paid gallery satisfies the
native single-source support, mask and divided-forcing contracts. The
support exponent is exactly the one used in the original representation.
No single test or field is chosen to construct the paying envelope. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal Source Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{d:ℕ}{V T I:Type}[DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

theorem original_singleton_format (F:Labels.Frame G d)(H:Hol G)(t:T)(a:V):
    (oneSource A F t a).Format (o a) H P:=by
  refine ⟨fun _=>(regular0 P.p _ (o a)).1,fun _=>mem_singleton_self _,fun _=>rfl,
    fun _ _=>vanishing0 d (o a) H,?_,?_,?_,?_,?_⟩
  · intro i U h
    apply A.K.charged t i U
    intro z
    exact h (by change (A.K.hard t i U).part (C.fire a)=0;rw [z];rfl)
  · intro i h
    obtain ⟨U,hU⟩:=Function.ne_iff.mp h
    exact (A.K.locality t i).carry U (C.fire a) hU a (mem_singleton_self a)
  · intro i k U
    exact congrArg (fun z:Poly C=>z.part (C.fire a)) ((A.K.locality t i).gauge k U)
  · intro i U W links flag
    exact congrArg (fun z:Poly C=>z.part (C.fire a)) ((A.K.locality t i).reads U W links flag)
  intro i
  exact (Poly.part_cont _).measurable.comp (A.K.locality t i).borel

theorem original_singleton_forced_stock {w:V→ℝ}(wp:∀v,0<w v){fee:ℝ}
    (paid:A.K.Paid w P.p.B P.p.supportExponent fee)(a:V):
    ∃b:ℕ→ℝ,(∀i,0≤b i) ∧ (∀t i U,‖(A.K.hard t i U).part (C.fire a)‖≤b i) ∧
      SumBudget (fun i=>P.p.mass (P.activities.forced i).support (b i)) (fee/w a):=by
  obtain ⟨f,hf,hit⟩:=paid.wages
  let S:=fun i=>(P.activities.forced i).support
  let b:=fun i=>if o a∈S i then ‖(f i).part (C.fire a)‖ else 0
  have bn(i):0≤b i:=by unfold b;split;exact norm_nonneg _;exact le_rfl
  refine ⟨b,bn,?_,?_⟩
  · intro t i U
    by_cases h:o a∈S i
    · rw [show b i=‖(f i).part (C.fire a)‖ from if_pos h]
      exact ((hf i t U (C.fire a)).1).trans_eq ((hf i t U).norm (C.fire a)).symm
    have z:(A.K.hard t i U).part (C.fire a)=0:=by
      by_contra hU;exact h ((A.K.locality t i).carry U (C.fire a) hU a (mem_singleton_self _))
    rw [z,norm_zero];exact bn _
  rw [div_eq_inv_mul]
  apply Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale (inv_nonneg.mpr (wp a).le) (hit (o a)))
  · intro i;exact mul_nonneg (Real.exp_pos _).le (bn i)
  intro i
  let E:=Real.exp (P.p.supportExponent*coverNumber P.p.B (S i))
  change E*(if o a∈S i then ‖(f i).part (C.fire a)‖ else 0)≤
    (w a)⁻¹*(if o a∈S i then Poly.price w (f i)*E else 0)
  by_cases h:o a∈S i
  · rw [if_pos h,if_pos h]
    have price:=Poly.member wp (C.fire a) (f i)
    rw [Poly.solo_toll] at price
    calc _=E*((w a)⁻¹*(w a*‖(f i).part (C.fire a)‖)):=by rw [inv_mul_cancel_left₀ (wp a).ne']
         _≤E*((w a)⁻¹*Poly.price w (f i)):=mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left price (inv_nonneg.mpr (wp a).le)) (Real.exp_pos _).le
         _=_:=by ring
  simp only [if_neg h,mul_zero,le_refl]

theorem original_singleton_remBound (F:Labels.Frame G d)(t:T)(a:V){w:V→ℝ}(wp:∀v,0<w v)
    {fee:ℝ}(paid:A.K.Paid w P.p.B P.p.supportExponent fee)(δ:ℝ)(hp:0<δ):
    (oneSource A F t a).remBound (o a) P δ ((fee/w a)/δ):=by
  obtain ⟨b,bn,price,book⟩:=original_singleton_forced_stock A wp paid a
  have non:=Push.AbsoluteSums.budget_nonneg book
  refine ⟨0,(fee/w a)/δ,le_rfl,div_nonneg non hp.le,by simp,hp,
      ⟨fun _=>0,budget0 _ _,fun _=>(regular0 P.p _ (o a)).2⟩,b,?_,fun i=>⟨bn i,price t i⟩⟩
  rwa [mul_div_cancel₀ _ hp.ne']

end YM.Integration.FVA1Physical.Exchange.RoseCut
