import YM.Integration.WilsonMeasuredPublicEntranceSignedEar
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldLine

/-! Price the signed regular exchange and its full compulsory remainder against one original nonconstant background. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldExchange
open Function Finset MeasureTheory Lattice RG Wilson Marker Poly OPE.Therm
open PhysicalNext PhysicalNext.Repeat Legato WilsonThermometerUnitFilingCoarse WilsonOriginalAlternativeHearing
open WilsonMeasuredPublicEntranceOrder WilsonMeasuredPublicEntranceCheapOrder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}{N p f:ℕ}
local notation "cfg" => Config G (R.family.side f p)
local notation "P" => R.family.path.rep N p f

open WilsonMeasuredPublicEntranceSignedEar (weighted cheap regular weighted_integrable)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)

theorem difference {b:ℕ}(F K:cfg→ℂ)(hf:Integrable F (prior G _))(hk:Integrable K (prior G _))
    (bf:b≤f)(W:Config G (R.family.side b p)):
    readingAt R (N:=N) (fun U=>F U-K U) bf W=readingAt R (N:=N) F bf W-readingAt R (N:=N) K bf W:=
  map_sub (WilsonOriginalMicroscopicEntranceHeldLine.ear R N p f b bf W) ⟨F,hf⟩ ⟨K,hk⟩

theorem numerical (live:f ≤ N){b:ℕ}(lo:b ≤ f)(W:Config G (R.family.side b p))(x e:V → cfg → ℂ)(n δ:V → ℝ)(vs:List V)
    (px:∀i U,‖x i U‖ ≤ n i)(pe:∀i U,‖e i U‖ ≤ δ i):
    ‖readingAt R (N:=N) (weighted (N:=N) R (cheap R x e vs)) lo W‖ ≤ route n (fun i=>n i+δ i) δ vs:=by
  have received:=normalized R.family N p R.makes live (weighted (N:=N) R (cheap R x e vs)) lo
  have hear:readingAt R (N:=N) (weighted (N:=N) R (cheap R x e vs)) lo W=
      held R.family N p (weighted (N:=N) R (cheap R x e vs)) lo W:=by
    simp only [readingAt,held,Complex.real_smul,Complex.ofReal_inv]
  rw [hear,received]
  apply actualTransport_norm_le R.family R.makes live _ lo
  intro U
  have nz:((P).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
  simp only [weighted,Complex.real_smul,Complex.ofReal_inv,←mul_assoc,inv_mul_cancel₀ nz,one_mul]
  exact price _ _ _ _ (fun i=>px i U) (fun i=>pe i U) vs


theorem original (live:f ≤ N){b:ℕ}(lo:b ≤ f)(W:Config G (R.family.side b p))(s:Finset V)(x y e ax ay az:V → cfg → ℂ)
    (hx:∀i,BoundedAt R.family (x i))(hy:∀i,BoundedAt R.family (y i))(he:∀i,BoundedAt R.family (e i))
    (sheet:∀i U,((P).eval U:ℂ)*(y i U-(x i U-e i U))=ax i U-ay i U-az i U)
    (n δ:V → ℝ)(px:∀i U,‖x i U‖ ≤ n i)(pe:∀i U,‖e i U‖ ≤ δ i)
    (T:ℝ)(int:Integrable (WilsonMeasuredPublicEntranceFlatShares.contact R s x y e ax ay az) (prior G _))
    (received:‖readingAt R (N:=N) (WilsonMeasuredPublicEntranceFlatShares.contact R s x y e ax ay az) lo W‖ ≤ T):
    let lifted:=fun F=>readingAt R (N:=N) (weighted (N:=N) R F) lo W
    let h:=WilsonMeasuredPublicEntranceFlatShares.contact R s x y e ax ay az
    lifted (factors x s.toList)-lifted (factors y s.toList)=lifted (cheap R x e s.toList)-readingAt R (N:=N) h lo W ∧
    ‖lifted (factors x s.toList)-lifted (factors y s.toList)‖ ≤ route n (fun i=>n i+δ i) δ s.toList+T:=by
  intro ear h
  have left:=weighted_integrable R live (collection R.family x hx s.toList)
  have right:=weighted_integrable R live (collection R.family y hy s.toList)
  have c:=weighted_integrable R live (regular R x e s.toList hx he)
  have field:(fun U=>weighted (N:=N) R (factors x s.toList) U-weighted (N:=N) R (factors y s.toList) U)=
      (fun U=>weighted (N:=N) R (cheap R x e s.toList) U-h U):=by
    funext U
    simp only [weighted,←mul_sub]
    exact WilsonMeasuredPublicEntranceCheapOrder.original _ _ _ _ _ (fun i=>sheet i U) s.toList
  have equality:ear (factors x s.toList)-ear (factors y s.toList)=ear (cheap R x e s.toList)-readingAt R (N:=N) h lo W:=by
    rw [←difference R (N:=N) _ _ left right lo W,
      ←difference R (N:=N) _ _ c int lo W,field]
  exact ⟨equality,equality ▸ (norm_sub_le ..).trans (add_le_add (numerical R live lo W x e n δ s.toList px pe) received)⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldExchange
end
