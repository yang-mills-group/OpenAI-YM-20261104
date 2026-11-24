import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionThreeTestCost

/-! Compare the seven original/impartial conditional moments on the full
two-particle fibre. An exceptional *pair* of fields is charged by its own
mixed normalized product mass. No good rectangle, or positive mass of an
arbitrarily chosen aperture, is required. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Filter Finset RG
open YM.Integration.FVA1Physical.Replica
open private proper_product_env from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionForestSevenAction
open private properCaps mean_cap funded_rows influence_wallet from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionThreeTestCost
open scoped Classical BigOperators
variable {X:Type*}[MeasurableSpace X]

def pairExcess (r:X→ℝ)(t:ℝ):Set (X×X):={z | t<cap (r z.1-r z.2)}

theorem pair_excess_borel {r:X→ℝ}(rm:Measurable r)(t:ℝ):MeasurableSet (pairExcess r t):=by
  exact measurableSet_lt measurable_const (show Measurable (fun z:X×X=>cap (r z.1-r z.2)) by unfold cap;fun_prop)

/-- Both unlike-law draws share the same physical exterior and kernel, with
their own complete normalizations. Correlation products are taken before
either expectation. The exceptional pair may depend on both entries. -/
theorem pair_excess_seven (μ:Measure X)[SFinite μ] {k a b r:X→ℝ}
    (km:Measurable k)(am:Measurable a)(bm:Measurable b)(kn:∀x,0≤k x)
    (ap:∀x,0<a x)(bp:∀x,0<b x)(rm:Measurable r)(anchor:ℝ)
    (same:∀x,Real.log (a x)-Real.log (b x)=r x+anchor)(t:ℝ)(tn:0≤t)
    (h:Fin 3→X→ℂ)(env:∀i,Envelope (h i))(L:Fin 3→ℝ)(ln:∀i,0≤L i)(pay:∀i x,‖h i x‖≤L i):
    let u:=fun x=>k x*a x;let v:=fun x=>k x*b x;let F:=physicalProperRows h
    let U:=fun i=>FrozenRead.meanOn μ u (F i);let V:=fun i=>FrozenRead.meanOn μ v (F i)
    let z:=∫x,u x ∂μ;let q:=∫x,v x ∂μ;let N:=fun s=>cost u v s+cost v u s
    Integrable u μ → Integrable v μ → 0<z → 0<q →
    ‖properThree U-properThree V‖≤(26*L 0*L 1*L 2)*
      (t+(∫s in pairExcess r t,N s ∂μ.prod μ)/(2*z*q)):=by
  intro u v F U V z q N ui vi zp qp
  let E:=pairExcess r t
  have mb:MeasurableSet E:=pair_excess_borel rm t
  let J:=fun x=>∑i:Fin 7,properWeights U V i*F i x
  let M:=26*L 0*L 1*L 2
  have mn:0≤M:=by dsimp only [M];positivity [ln 0,ln 1,ln 2]
  have un(x):0≤u x:=mul_nonneg (kn x) (ap x).le
  have vn(x):0≤v x:=mul_nonneg (kn x) (bp x).le
  have uf(i):‖U i‖≤properCaps L i:=mean_cap (km.mul am) ui un zp (funded_rows h L ln pay i)
  have vf(i):‖V i‖≤properCaps L i:=mean_cap (km.mul bm) vi vn qp (funded_rows h L ln pay i)
  have jcap(x):‖J x‖≤13*L 0*L 1*L 2:=influence_wallet h L ln pay U V uf vf x
  have dia(x y:X):‖J x-J y‖≤M:=(norm_sub_le ..).trans ((add_le_add (jcap x) (jcap y)).trans_eq (by dsimp only [M];ring))
  have allSeven:Envelope J:=Multi.Leaf.amounts univ (fun i x=>properWeights U V i*F i x)
    (fun i=>Multi.Leaf.multiply (Multi.Leaf.atom _) (proper_product_env h env i))
  let η:=μ.prod μ
  have inl:Integrable (cost u v) η:=ui.mul_prod vi
  have inr:Integrable (cost v u) η:=vi.mul_prod ui
  have ni:Integrable N η:=inl.add inr
  have nn(s):0≤N s:=add_nonneg (mul_nonneg (un _) (vn _)) (mul_nonneg (vn _) (un _))
  have nsum:(∫s,N s ∂η)=2*z*q:=by
    rw [show (∫s,N s ∂η)=(∫s,cost u v s ∂η)+(∫s,cost v u s ∂η) from integral_add inl inr]
    change (∫s,u s.1*v s.2 ∂μ.prod μ)+(∫s,v s.1*u s.2 ∂μ.prod μ)=_
    rw [integral_prod_mul,integral_prod_mul];ring
  have bounded(s:X×X):actionBill u v r s ≤ N s*t+E.indicator N s:=by
    change N s*cap (r s.1-r s.2)≤N s*t+_
    by_cases inE:s∈E
    · rw [Set.indicator_of_mem inE]
      exact (mul_le_of_le_one_right (nn _) (min_le_left ..)).trans (le_add_of_nonneg_left (mul_nonneg (nn _) tn))
    rw [Set.indicator_of_notMem inE,add_zero]
    exact mul_le_mul_of_nonneg_left (le_of_not_gt inE) (nn _)
  have orig(s):0≤actionBill u v r s:=mul_nonneg (nn s) (le_min zero_le_one (by positivity [abs_nonneg (r s.1-r s.2)]))
  have compare:(∫s,actionBill u v r s*‖J s.1-J s.2‖ ∂η)≤M*(2*z*q*t+∫s in E,N s ∂η):=by
    calc
      _≤∫s,(N s*t+E.indicator N s)*M ∂η:=by
        apply integral_mono (cost_times_diameter (integrable_bill ui vi un vn rm) allSeven) (((ni.mul_const t).add (ni.indicator mb)).mul_const M)
        intro s
        exact (mul_le_mul_of_nonneg_left (dia ..) (orig s)).trans (mul_le_mul_of_nonneg_right (bounded s) mn)
      _=_:=by rw [integral_mul_const,integral_add (ni.mul_const t) (ni.indicator mb),integral_mul_const,nsum,integral_indicator mb];ring
  have original:=(seven_signed_action μ km am bm kn ap bp rm anchor same F (proper_product_env h env) ui vi zp qp).2
  have fee:(2*z*q)*‖properThree U-properThree V‖≤M*(2*z*q*t+∫s in E,N s ∂η):=original.trans compare
  have cash:=mul_pos (mul_pos (by norm_num:(0:ℝ)<2) zp) qp
  have eq:(2*z*q)*(M*(t+(∫s in E,N s ∂η)/(2*z*q)))=M*(2*z*q*t+∫s in E,N s ∂η):=by
    field_simp [zp.ne',qp.ne']
  exact le_of_mul_le_mul_left (fee.trans_eq eq.symm) cash

end YM.Integration.FVA1Physical.Exchange.RoseCut
