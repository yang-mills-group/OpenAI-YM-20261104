import YM.Integration.WilsonOriginalSeparatedHardReturn

/-! Complete forced selections depend affinely on the price of marked old
operands that contain one shared true label. Each selection retains its
original flag and every unselected partner. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonForcedMarkerLine
open Set Filter Finset Lattice Wilson RG Ac Marker RG3
open scoped Topology BigOperators Classical
variable {V ι : Type*} [DecidableEq V] {R : Marker.Census V} {v : V} {q : ℂ}

def pinned (v : V) (f : Poly R) : Prop :=
  ∀ s:R.Mode,v∉s.val → f.part s=0

theorem pin_zero : pinned v (0:Poly R) := fun _ _=>rfl

theorem pin_sum {f g:Poly R} (h : pinned v f) (k : pinned v g) : pinned v (f+g) :=
  fun s hs=>by rw [Poly.part_plus,h s hs,k s hs,add_zero]

theorem pin_left {f:Poly R} (h : pinned v f) (g:Poly R) : pinned v (f*g) := by
  intro m hm
  rw [Poly.part_mul]
  apply sum_eq_zero; intro s _
  apply sum_eq_zero; intro t _
  split
  next merged =>
    have miss : v∉s.val := fun hv=>hm (merged.2 ▸ Finset.mem_union_left _ hv)
    rw [h s miss,zero_mul]
  next => rfl

theorem square {f g:Poly R} (h : pinned v f) (k : pinned v g) : f*g=0 := by
  ext1 m
  rw [Poly.part_mul,Poly.part_nil]
  apply sum_eq_zero; intro s _
  apply sum_eq_zero; intro t _
  split
  next merged =>
    by_cases hs:v∈s.val
    · rw [k t (fun ht=>Finset.disjoint_left.mp merged.1 hs ht),mul_zero]
    · rw [h s hs,zero_mul]
  next => rfl

structure Line (v : V) (q : ℂ) (empty trueRow raised : Poly R) : Prop where
  marked : pinned v (raised-empty)
  value : trueRow = empty + q • (raised-empty)

theorem same (p:Poly R) : Line v q p p p := by
  constructor <;> simp [pinned]

theorem product {a b c d e f:Poly R} (A:Line v q a b c) (B:Line v q d e f) :
    Line v q (a*d) (b*e) (c*f) := by
  let z:= c-a
  let w:= f-d
  have vanish : z*w=0 := square A.marked B.marked
  have hc : c=a+z := by dsimp only [z]; abel
  have hf : f=d+w := by dsimp only [w]; abel
  have diff : c*f-a*d = z*d + a*w := by
    rw [hc,hf,add_mul,mul_add,mul_add,vanish]; abel
  have pa : pinned v (a*w) := mul_comm w a ▸ pin_left B.marked a
  refine ⟨diff ▸ pin_sum (pin_left A.marked d) pa,?_⟩
  rw [A.value,B.value,diff]
  change (a+q • z)*(d+q • w)=a*d+q • (z*d+a*w)
  rw [←Poly.product_bead,←Poly.product_bead,←Poly.product_bead]
  calc
    _ = a*d+Poly.bead R q*(z*d+a*w)+(Poly.bead R q)^2*(z*w) := by ring
    _ = _ := by rw [vanish,mul_zero,add_zero]

theorem products (s:Finset ι) (a b c:ι→Poly R) (h:∀ i∈s,Line v q (a i) (b i) (c i)) :
    Line v q (∏ i∈s,a i) (∏ i∈s,b i) (∏ i∈s,c i) := by
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using (same (v:=v) (q:=q) (1 : Poly R))
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact product (h i (Finset.mem_insert_self ..)) (ih fun z hz=>h z (Finset.mem_insert_of_mem hz))

/-- Actual flags, old exclusion and complete native support in one Kiosk
merger. Applies unchanged to the second merger with the actual mask slips. -/
theorem merged {n:Side} (F:Letters.Frame n ι) (bad:Support n) (a b c:ι→Poly R)
    (h:∀ i,Line v q (a i) (b i) (c i)) (p:F.Patch) :
    Line v q (F.merged bad a p) (F.merged bad b p) (F.merged bad c p) := by
  unfold Letters.Frame.merged
  split
  · exact products _ _ _ _ (fun i _=>h i)
  · exact same _

end YM.Integration.WilsonForcedMarkerLine
end
