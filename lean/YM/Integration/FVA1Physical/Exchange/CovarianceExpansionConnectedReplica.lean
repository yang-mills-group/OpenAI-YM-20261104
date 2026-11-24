import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionReplicaAfterHearing
import YM.Next.MULTISOURCE.Measure

/-! The connected two-field observable under the two true positive
normalizations. The two singleton means keep their respective laws. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Replica
open MeasureTheory RG
open scoped Classical
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def fieldCovariance (μ:Measure X) (u:X→ℝ) (f h:X→ℂ):ℂ :=
  FrozenRead.meanOn μ u (fun x=>f x*h x)- FrozenRead.meanOn μ u f * FrozenRead.meanOn μ u h

/-- Three action covariations on the same two positive laws pay the full
connected screening. The constants in front of the single-source bills are
the two actual one-point readings, even when one is zero. -/
theorem connected_action_price {k a b r:X→ℝ}
    (kn:∀x,0≤k x)(ap:∀x,0<a x)(bp:∀x,0<b x)(rm:Measurable r)
    (anchor:ℝ)(same:∀x,Real.log (a x)-Real.log (b x)=r x+anchor)
    {f h:X→ℂ}(fe:Envelope f)(he:Envelope h):
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x
    let A:=∫x,u x ∂μ;let B:=∫x,v x ∂μ
    let toll:=fun F:X→ℂ=>∫z,actionBill u v r z*‖F z.1-F z.2‖ ∂μ.prod μ
    Integrable u μ → Integrable v μ → 0<A → 0<B →
    2*A*B*‖fieldCovariance μ u f h - fieldCovariance μ v f h‖ ≤
      toll (fun x=>f x*h x)+‖FrozenRead.meanOn μ u h‖*toll f+‖FrozenRead.meanOn μ v f‖*toll h := by
  intro u v A B toll ui vi up vp
  let Q:=2*A*B
  have qp:0≤Q:= (mul_pos (mul_pos (by norm_num) up) vp).le
  have price (F:X→ℂ)(e:Envelope F):Q*‖FrozenRead.meanOn μ u F-FrozenRead.meanOn μ v F‖≤toll F:=
    reading kn ap bp rm anchor same e ui vi up vp
  let F:=fun x=>f x*h x
  have cross:Envelope F:=Multi.Leaf.multiply fe he
  let x:=FrozenRead.meanOn μ u f;let y:=FrozenRead.meanOn μ v f
  let k':=FrozenRead.meanOn μ u h;let l:=FrozenRead.meanOn μ v h
  let m:=FrozenRead.meanOn μ u F;let n:=FrozenRead.meanOn μ v F
  have exactCov:fieldCovariance μ u f h - fieldCovariance μ v f h =
      (m-n) - (x-y)*k' - y*(k'-l) := by
    dsimp only [fieldCovariance,x,y,k',l,m,n,F];ring
  have tri:‖(m-n)-(x-y)*k'-y*(k'-l)‖≤‖m-n‖+‖x-y‖*‖k'‖+‖y‖*‖k'-l‖:=by
    apply (norm_sub_le ..).trans
    rw [norm_mul]
    exact add_le_add ((norm_sub_le (m-n) ((x-y)*k')).trans_eq (by rw [norm_mul])) (le_refl _)
  rw [exactCov]
  calc Q*‖(m-n)-(x-y)*k'-y*(k'-l)‖ ≤ Q*(‖m-n‖+‖x-y‖*‖k'‖+‖y‖*‖k'-l‖) :=
          mul_le_mul_of_nonneg_left tri qp
       _=Q*‖m-n‖+‖k'‖*(Q*‖x-y‖)+‖y‖*(Q*‖k'-l‖):=by ring
       _≤_:=add_le_add (add_le_add (price F cross) (mul_le_mul_of_nonneg_left (price f fe) (norm_nonneg _)))
              (mul_le_mul_of_nonneg_left (price h he) (norm_nonneg _))

end YM.Integration.FVA1Physical.Replica
