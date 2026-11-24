import YM.Integration.WilsonOriginalOccupiedFieldLayout

/-! One fixed occupied lift and the real full-period deck orbit recover the whole filed marked field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPinnedDeckOrbit
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder.Floe Comparison.RG02 Multi Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalLocatedDeckAction WilsonOriginalConnectedPeriodPage
open WilsonOriginalJointDeckMotion WilsonEmittedRootedJetWage WilsonOriginalOccupiedFieldLayout
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (v:s.val)

def around (x:Site n)(b:PagesOf n N):Deck h ≃ PagesOf n N where
  toFun a:=step h x a b
  invFun c:=⟨(page h x c).val-(page h x b).val,by change splitter h _=0;rw [map_sub,below,below,sub_self]⟩
  left_inv a:=by apply Subtype.ext;change (page h x (step h x a b)).val- _=_;rw [value,add_sub_cancel_right]
  right_inv c:=by
    apply (page h x).injective;apply Subtype.ext;rw [value]
    exact sub_add_cancel _ _

def needle (j:ℕ) (b:PagesOf n N):Joint G N→ℂ:=shade h M t j (fun i p=>(M i).mode=s ∧ index h (M i) p v.val=b)

theorem moved (j:ℕ) (b:PagesOf n N) (a:Deck h) (z:Joint G N):
    needle h M t s v j (step h (o.origin v.val) a b) (motion G a.val z)=needle h M t s v j b z:=by
  unfold needle shade frame
  apply congrArg (fun q:ℂ=>(z.1^j:ℝ)*q)
  apply tsum_congr;intro i
  rw [←Equiv.sum_comp (steps h (M i).center a)]
  apply sum_congr rfl
  intro p _
  by_cases ok:(M i).mode=s
  · have used:v.val∈(M i).mode.val:=ok.symm ▸ v.property
    simp only [ok,true_and]
    change (if index h (M i) (step h (M i).center a p) v.val=step h (o.origin v.val) a b then _ else _)=_
    rw [roots h (M i) p a v.val used]
    have same:step h (o.origin v.val) a (index h (M i) p v.val)=step h (o.origin v.val) a b ↔ index h (M i) p v.val=b:=(steps h (o.origin v.val) a).injective.eq_iff
    simp only [same]
    split_ifs with atb
    · unfold token
      exact congrArg (fun q:ℝ=>(M i).paint t*(q:ℂ)) (marked h (M i) p a z)
    · rfl
  · simp [ok]

theorem most {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j:ℕ) (z:Joint G N):
    (∑b:PagesOf n N,needle h M t s v j b z)=shade h M t j (fun i _=>(M i).mode=s) z:=by
  unfold needle shade frame
  rw [←mul_sum]
  apply congrArg (fun q:ℂ=>(z.1^j:ℝ)*q)
  let keep (b:PagesOf n N)(i:ι)(p:PagesOf n N):Prop:=(M i).mode=s ∧ index h (M i) p v.val=b
  let draw (b:PagesOf n N)(i:ι)(p:PagesOf n N):ℂ:=@ite ℂ (keep b i p) (Classical.propDecidable _) (token h M t i p z) 0
  have sell (b:PagesOf n N):Summable (fun i=>∑p:PagesOf n N,draw b i p):=
    summable_sum fun p _=>collects h M t stock hs (keep b) p z
  change (∑b:PagesOf n N,∑'i,∑p:PagesOf n N,draw b i p)=_
  rw [←Summable.tsum_finsetSum (fun b _=>sell b)]
  apply tsum_congr;intro i
  rw [sum_comm]
  apply sum_congr rfl;intro p _
  by_cases eq:(M i).mode=s <;> simp [draw,keep,eq]

theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j:ℕ) (b:PagesOf n N) (x:Site N):
    WilsonOriginalPolarizedAngularPage.board h x (motion G) (needle h M t s v j b)=shade h M t j (fun i _=>(M i).mode=s):=by
  funext z
  let read:=fun y:Site N=>needle h M t s v j b (motion G (y-x) z)
  calc
    _ = ∑p:PagesOf n N,read (page h (splitter h x) p).val:=by simp only [WilsonOriginalPolarizedAngularPage.board,Finset.sum_apply,comp_apply,read]
    _ = ∑a:Deck h,read (a.val+x):=WilsonOriginalConnectedPeriodPage.pages h x read
    _ = ∑a:Deck h,needle h M t s v j (step h (o.origin v.val) (-a) b) z:=by
      apply sum_congr rfl;intro a _
      have F:=moved h M t s v j (step h (o.origin v.val) (-a) b) a z
      have restored:step h (o.origin v.val) a (step h (o.origin v.val) (-a) b)=b:=(steps h (o.origin v.val) a).right_inv b
      simpa [read,restored] using F
    _ = ∑q:PagesOf n N,needle h M t s v j q z:=
      Equiv.sum_comp ((Equiv.neg (Deck h)).trans (around h (o.origin v.val) b)) (fun q=>needle h M t s v j q z)
    _ = _:=most h M t s v stock hs j z

end YM.Integration.WilsonOriginalPinnedDeckOrbit
