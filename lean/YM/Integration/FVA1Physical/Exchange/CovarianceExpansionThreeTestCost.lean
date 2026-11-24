import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionForestSevenAction
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSevenAperture

/-! A genuinely paid test oscillation, including the proper-face constants.
The three separate wallets multiply exactly once, irrespective of the reference
conditional normalization. Thus any further exceptional probability is paid
under the original law only. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Finset Filter RG Matrix
open scoped Classical BigOperators
open private proper_product_env from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionForestSevenAction
open private fibre_prob fibre_reading from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
variable {X:Type*}[MeasurableSpace X]

private theorem mean_cap {μ:Measure X}{u:X→ℝ} (um:Measurable u)(ui:Integrable u μ)
    (un:∀x,0≤u x)(up:0<∫x,u x ∂μ) {F:X→ℂ}{M:ℝ}(limit:∀x,‖F x‖≤M):
    ‖FrozenRead.meanOn μ u F‖≤M:=by
  let ν:=fibreLaw μ u
  letI:=fibre_prob μ ui un up
  rw [←fibre_reading μ um un up]
  simpa using norm_integral_le_of_norm_le_const (μ:=ν) (.of_forall limit)

private def properCaps (L:Fin 3→ℝ):Fin 7→ℝ:=
  ![L 0,L 1,L 2,L 0*L 1,L 0*L 2,L 1*L 2,L 0*L 1*L 2]

omit [MeasurableSpace X] in
private theorem funded_rows (h:Fin 3→X→ℂ)(L:Fin 3→ℝ)(ln:∀i,0≤L i)
    (pay:∀i x,‖h i x‖≤L i)(s:Fin 7)(x:X):‖physicalProperRows h s x‖≤properCaps L s:=by
  have two(i j:Fin 3):‖h i x*h j x‖≤L i*L j:=by
    rw [norm_mul];exact mul_le_mul (pay i x) (pay j x) (norm_nonneg _) (ln _)
  fin_cases s
  · exact pay 0 x
  · exact pay 1 x
  · exact pay 2 x
  · exact two 0 1
  · exact two 0 2
  · exact two 1 2
  · change ‖h 0 x*h 1 x*h 2 x‖≤_
    rw [norm_mul];exact mul_le_mul (two 0 1) (pay 2 x) (norm_nonneg _) (mul_nonneg (ln 0) (ln 1))

private def dualCaps(L:Fin 3→ℝ):Fin 7→ℝ:=
  ![3*L 1*L 2,3*L 0*L 2,3*L 0*L 1,L 2,L 1,L 0,1]

private theorem weight_wallet (u v:Fin 7→ℂ)(L:Fin 3→ℝ)(ln:∀i,0≤L i)
    (pu:∀s,‖u s‖≤properCaps L s)(pv:∀s,‖v s‖≤properCaps L s)(s:Fin 7):
    ‖properWeights u v s‖≤dualCaps L s:=by
  have one {c a b:ℂ}{A B:ℝ}(an:0≤A)(cn:‖c‖≤A*B)(af:‖a‖≤A)(bf:‖b‖≤B):
      ‖-c+2*a*b‖≤3*A*B:=by
    refine (norm_add_le ..).trans ?_
    rw [norm_neg,norm_mul,norm_mul,show ‖(2:ℂ)‖=2 by norm_num]
    have bound:=mul_le_mul (mul_le_mul_of_nonneg_left af (by norm_num : (0:ℝ)≤2)) bf
      (norm_nonneg _) (mul_nonneg (by norm_num) an)
    calc _≤A*B+2*A*B:=add_le_add cn bound
         _=_:=by ring
  fin_cases s
  · exact one (ln 1) (pv 5) (pu 1) (pu 2)
  · exact one (ln 0) (pv 4) (pv 0) (pu 2)
  · exact one (ln 0) (pv 3) (pv 0) (pv 1)
  · simpa [properWeights,dualCaps,properCaps] using pu 2
  · simpa [properWeights,dualCaps,properCaps] using pu 1
  · simpa [properWeights,dualCaps,properCaps] using pu 0
  · simp [properWeights,dualCaps]

omit [MeasurableSpace X] in
private theorem influence_wallet (h:Fin 3→X→ℂ)(L:Fin 3→ℝ)(ln:∀i,0≤L i)
    (pay:∀i x,‖h i x‖≤L i)(u v:Fin 7→ℂ)
    (pu:∀s,‖u s‖≤properCaps L s)(pv:∀s,‖v s‖≤properCaps L s)(x:X):
    ‖∑i:Fin 7,properWeights u v i*physicalProperRows h i x‖≤13*L 0*L 1*L 2:=by
  calc
    _≤∑i:Fin 7,‖properWeights u v i*physicalProperRows h i x‖ := norm_sum_le ..
    _≤∑i:Fin 7,dualCaps L i*properCaps L i:=by
      apply sum_le_sum;intro i _
      have dc:0≤dualCaps L i:=(norm_nonneg _).trans (weight_wallet u v L ln pu pv i)
      rw [norm_mul];exact mul_le_mul (weight_wallet u v L ln pu pv i) (funded_rows h L ln pay i x) (norm_nonneg _) dc
    _= _:=by simp [properCaps,dualCaps,Fin.sum_univ_succ];ring

/-- The reference may have no integrable continuation outside the aperture.
The second estimate buys even the absolute exceptional integral using only the
probability cost in the original law. The first keeps its signed value. -/
theorem funded_seven_aperture {μ:Measure X}[SFinite μ] (B:Set X)(bm:MeasurableSet B)
    {k a b r:X→ℝ}(km:Measurable k)(am:Measurable a)(bb:Measurable b)(kn:∀x,0≤k x)
    (ap:∀x,0<a x)(bp:∀x,0<b x)(rm:Measurable r)(anchor:ℝ)
    (same:∀x,Real.log (a x)-Real.log (b x)=r x+anchor)
    (t:ℝ)(tn:0≤t)(fee:∀x∈B,∀y∈B,Replica.cap (r x-r y)≤t)
    (h:Fin 3→X→ℂ)(eh:∀i,Envelope (h i))(L:Fin 3→ℝ)(ln:∀i,0≤L i)(pay:∀i x,‖h i x‖≤L i):
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x;let ν:=μ.restrict B;let F:=physicalProperRows h
    let U:=fun i=>FrozenRead.meanOn μ u (F i);let V:=fun i=>FrozenRead.meanOn ν v (F i)
    let J:=fun x=>∑i:Fin 7,properWeights U V i*F i x
    let Q:=FrozenRead.meanOn ν v J
    let z:=∫x,u x ∂μ;let c:=∫x,u x ∂ν;let q:=∫x,v x ∂ν;let M:=26*L 0*L 1*L 2
    Integrable u μ→Integrable v ν→0<z→0<c→0<q→
    z*‖properThree U-properThree V‖≤c*t*M+‖∫x in Bᶜ,u x • (J x-Q) ∂μ‖ ∧
    z*‖properThree U-properThree V‖≤M*(c*t+∫x in Bᶜ,u x ∂μ):=by
  intro u v ν F U V J Q z c q M ui vi zp cp qp
  have un(x):0≤u x:=mul_nonneg (kn x) (ap x).le
  have vn(x):0≤v x:=mul_nonneg (kn x) (bp x).le
  have uf(i):‖U i‖≤properCaps L i:=mean_cap (km.mul am) ui un zp (funded_rows h L ln pay i)
  have vf(i):‖V i‖≤properCaps L i:=mean_cap (km.mul bb) vi vn qp (funded_rows h L ln pay i)
  let half:=13*L 0*L 1*L 2
  have jcap(x):‖J x‖≤half:=influence_wallet h L ln pay U V uf vf x
  have qcap:‖Q‖≤half:=mean_cap (km.mul bb) vi vn qp jcap
  have twice:half+half=M:=by dsimp only [half,M];ring
  have price:=signed_seven_aperture (μ:=μ) B bm km am bb kn ap bp rm anchor same t tn fee F (proper_product_env h eh) ui vi zp cp qp
  have signed:z*‖properThree U-properThree V‖≤c*t*M+‖∫x in Bᶜ,u x • (J x-Q) ∂μ‖:=
    price.2 M fun x _ y _=> (norm_sub_le ..).trans ((add_le_add (jcap x) (jcap y)).trans_eq twice)
  have off:=norm_integral_le_of_norm_le (μ:=μ.restrict Bᶜ) (ui.integrableOn.mul_const M)
    (.of_forall fun x=>show ‖u x • (J x-Q)‖≤u x*M from by
      rw [norm_smul,Real.norm_of_nonneg (un x)]
      exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans ((add_le_add (jcap x) qcap).trans_eq twice)) (un x))
  rw [integral_mul_const] at off
  refine ⟨signed,?_⟩
  calc
    _≤c*t*M+(∫x in Bᶜ,u x ∂μ)*M:=signed.trans (add_le_add le_rfl off)
    _=_:=by ring
end YM.Integration.FVA1Physical.Exchange.RoseCut
