import YM.Integration.WilsonOriginalSignedHardHearing
import YM.Integration.WilsonThermometerCenteredAlgebra
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedAmplitude
open Finset Lattice Wilson RG Ac Marker QuadraticLocal Comparison.RG02.Order
open scoped Classical BigOperators
variable {R:Marker.Census (Fin 3)} {ι:Type*} {q:ℂ} {a b c f g h:Poly R}

/-- Only old mixed coefficients change. Their native roots remain present in the polynomial. -/
def mixed (x:Poly R):Prop:=∀s:R.Mode,s.val.card ≤ 1 → x.part s=0

theorem plus {x y:Poly R} (hx:mixed x)(hy:mixed y):mixed (x+y):=
  fun s hs=>by rw [Poly.part_plus,hx s hs,hy s hs,add_zero]

theorem times {x:Poly R}(hx:mixed x)(y:Poly R):mixed (x*y):=by
  intro m hm
  rw [Poly.part_mul]
  apply sum_eq_zero;intro s _
  apply sum_eq_zero;intro t _
  split
  next merged =>
    have bound:s.val.card ≤ m.val.card:=card_le_card (merged.2 ▸ subset_union_left)
    rw [hx s (bound.trans hm),zero_mul]
  next =>rfl

theorem square {x y:Poly R}(hx:mixed x)(hy:mixed y):x*y=0:=by
  ext1 m
  rw [Poly.part_mul,Poly.part_nil]
  apply sum_eq_zero;intro s _
  apply sum_eq_zero;intro t _
  split
  next merged =>
    have span:s.val.card+t.val.card ≤ 3:=by
      rw [←card_union_of_disjoint merged.1]
      exact card_le_univ _
    by_cases few:s.val.card ≤ 1
    · rw [hx s few,zero_mul]
    · rw [hy t (by omega),mul_zero]
  next =>rfl

structure Line (q:ℂ)(erased ordinary raised:Poly R):Prop where
  marked : mixed (raised-erased)
  value : ordinary=erased+q • (raised-erased)

/-- Retain the quiet and the three singleton parts; multiply every old mixed part by x. -/
def reprice (x:ℂ)(p:Poly R):Poly R:=Poly.inject fun s=>if s.val.card ≤ 1 then p.part s else x*p.part s

theorem taps (T:ℂ)(inverse:q*T=1)(p:Poly R):Line q (reprice 0 p) p (reprice T p):=by
  constructor
  · intro s few
    change (if s.val.card ≤ 1 then p.part s else T*p.part s)-
      (if s.val.card ≤ 1 then p.part s else 0*p.part s)=0
    simp [few]
  · ext1 s
    change p.part s=(if s.val.card ≤ 1 then p.part s else 0*p.part s)+q*
      ((if s.val.card ≤ 1 then p.part s else T*p.part s)-(if s.val.card ≤ 1 then p.part s else 0*p.part s))
    by_cases few:s.val.card ≤ 1
    · simp [few]
    · simp [few,←mul_assoc,inverse]

theorem same (p:Poly R):Line q p p p:=by constructor <;> simp [mixed]

theorem scaled (L:Line q a b c)(k:ℂ):Line q (k • a) (k • b) (k • c):=by
  constructor
  · intro s few;rw [←smul_sub,Poly.part_smul,L.marked s few,mul_zero]
  · rw [L.value,smul_add,←smul_sub,smul_comm k q]

theorem add (L:Line q a b c)(K:Line q f g h):Line q (a+f) (b+g) (c+h):=by
  have diff:(c+h)-(a+f)=(c-a)+(h-f):=by abel
  refine ⟨diff ▸ plus L.marked K.marked,?_⟩
  rw [L.value,K.value,diff,smul_add];abel

theorem product (L:Line q a b c)(K:Line q f g h):Line q (a*f) (b*g) (c*h):=by
  let z:=c-a
  let w:=h-f
  have nil:z*w=0:=square L.marked K.marked
  have e1:c=a+z:=by dsimp only [z];abel
  have e2:h=f+w:=by dsimp only [w];abel
  have diff:c*h-a*f=z*f+a*w:=by rw [e1,e2,add_mul,mul_add,mul_add,nil];abel
  have chip:mixed (a*w):=mul_comm w a ▸ times K.marked a
  refine ⟨diff ▸ plus (times L.marked f) chip,?_⟩
  rw [L.value,K.value,diff]
  change (a+q • z)*(f+q • w)=a*f+q • (z*f+a*w)
  rw [←Poly.product_bead,←Poly.product_bead,←Poly.product_bead]
  calc
    _ = a*f+Poly.bead R q*(z*f+a*w)+(Poly.bead R q)^2*(z*w):=by ring
    _ = _:=by rw [nil,mul_zero,add_zero]

theorem power (L:Line q a b c)(n:ℕ):Line q (a^n) (b^n) (c^n):=by
  induction n with
  | zero =>simpa using (same (q:=q) (1:Poly R))
  | succ k ih=>simpa only [pow_succ] using product ih L

theorem finite (S:Finset ι)(A K F:ι→Poly R)(lines:∀i∈S,Line q (A i) (K i) (F i)):
    Line q (∑i∈S,A i) (∑i∈S,K i) (∑i∈S,F i):=by
  induction S using Finset.induction_on with
  | empty =>simpa using (same (q:=q) (0:Poly R))
  | insert i s fresh ih =>
    simp only [sum_insert fresh]
    exact add (lines i (mem_insert_self _ _)) (ih (fun j hj=>lines _ (mem_insert_of_mem hj)))

theorem products (S:Finset ι)(A K F:ι→Poly R)(lines:∀i∈S,Line q (A i) (K i) (F i)):
    Line q (∏i∈S,A i) (∏i∈S,K i) (∏i∈S,F i):=by
  induction S using Finset.induction_on with
  | empty =>simpa using (same (q:=q) (1:Poly R))
  | insert i s fresh ih =>
    simp only [prod_insert fresh]
    exact product (lines i (mem_insert_self _ _)) (ih (fun j hj=>lines _ (mem_insert_of_mem hj)))

theorem series (A K F:ι→Poly R)(base:Summable A)(raised:Summable F)(lines:∀i,Line q (A i) (K i) (F i)):
    Line q (∑'i,A i) (∑'i,K i) (∑'i,F i):=by
  constructor
  · intro s few
    rw [←raised.tsum_sub base,Poly.share (raised.sub base)]
    simpa only [tsum_zero] using (tsum_congr (fun i=>(lines i).marked s few))
  · have eq:K=fun i=>A i+q • (F i-A i):=funext (fun i=>(lines i).value)
    rw [eq]
    exact (base.hasSum.add ((raised.hasSum.sub base.hasSum).const_smul q)).tsum_eq

theorem passed (L:Line q a b c):Line q (Poly.pass a) (Poly.pass b) (Poly.pass c):=
  finite _ _ _ _ (fun i _=>scaled (power L i) _)

theorem connected (L:Line q a b c)(n:ℕ):Line q (logTo n a) (logTo n b) (logTo n c):=by
  have step:Line q (1-a) (1-b) (1-c):=by
    simpa only [neg_one_smul,sub_eq_add_neg] using add (same (q:=q) (1:Poly R)) (scaled L (-1))
  exact finite (range n) _ _ _ (fun i _=>scaled (power step (i+1)) _)

end YM.Integration.WilsonThermometerMixedAmplitude
