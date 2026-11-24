import YM.Integration.WilsonMarkedIndependentMixedMeasurement

/-! Closure of a signed finite/cover estimate under the continuous
bilinear products in the complete measured formal moment. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedMomentPrice
open Function Filter Finset
open scoped Classical BigOperators Topology
variable {U V W α:Type}[NormedAddCommGroup U][NormedAddCommGroup V][NormedAddCommGroup W]
variable {m:ℕ}{t:ℕ→ℝ}

def Earned {U:Type}[NormedAddCommGroup U](m:ℕ)(t:ℕ→ℝ)(X Y:ℕ→ℕ→U):Prop:=
  ∃C:ℝ,0≤C ∧ ∀ᶠp:ℕ in atTop,∀N,m≤N →
    ‖X N p‖≤C ∧ ‖Y N p‖≤C ∧ ‖X N p-Y N p‖≤C*t p

theorem constant (m:ℕ)(t:ℕ→ℝ)(ht:∀p,0≤t p)(v:U):
    Earned m t (fun _ _=>v) (fun _ _=>v):=by
  refine ⟨‖v‖,norm_nonneg _,Eventually.of_forall fun p N _=>⟨le_rfl,le_rfl,?_⟩⟩
  rw [sub_self,norm_zero];exact mul_nonneg (norm_nonneg _) (ht p)

theorem add {X Y F H:ℕ→ℕ→U}(left:Earned m t X Y)(right:Earned m t F H):
    Earned m t (fun n p=>X n p+F n p) (fun n p=>Y n p+H n p):=by
  obtain ⟨a,ap,ha⟩:=left
  obtain ⟨b,bp,hb⟩:=right
  refine ⟨a+b,add_nonneg ap bp,?_⟩
  filter_upwards [ha,hb] with p h k
  intro n stop
  obtain ⟨x,y,z⟩:=h n stop
  obtain ⟨u,v,w⟩:=k n stop
  refine ⟨(norm_add_le ..).trans (add_le_add x u),(norm_add_le ..).trans (add_le_add y v),?_⟩
  rw [show X n p+F n p-(Y n p+H n p)=(X n p-Y n p)+(F n p-H n p) by abel, add_mul]
  exact (norm_add_le ..).trans (add_le_add z w)

theorem smul [NormedSpace ℝ U]{X Y:ℕ→ℕ→U}(a:ℝ)(h:Earned m t X Y):
    Earned m t (fun n p=>a • X n p) (fun n p=>a • Y n p):=by
  obtain ⟨B,hB,paid⟩:=h
  refine ⟨‖a‖*B,mul_nonneg (norm_nonneg _) hB,?_⟩
  filter_upwards [paid] with p issued
  intro n eligible
  obtain ⟨x,y,z⟩:=issued n eligible
  simp only [←smul_sub,norm_smul,mul_assoc]
  exact ⟨mul_le_mul_of_nonneg_left x (norm_nonneg _),mul_le_mul_of_nonneg_left y (norm_nonneg _),
    mul_le_mul_of_nonneg_left z (norm_nonneg _)⟩

theorem summed (ht:∀p,0≤t p)(S:Finset α)(f g:α→ℕ→ℕ→U)(h:∀i∈S,Earned m t (f i) (g i)):
    Earned m t (fun n p=>∑i∈S,f i n p) (fun n p=>∑i∈S,g i n p):=by
  classical
  induction S using Finset.induction_on with
  | empty=>simpa using constant m t ht (0:U)
  | @insert a s absent ih=>
    simp only [sum_insert absent]
    exact add (h a (mem_insert_self ..)) (ih fun i hi=>h i (mem_insert_of_mem hi))

theorem mapped [NormedSpace ℝ U][NormedSpace ℝ V](M:U→L[ℝ]V){X Y:ℕ→ℕ→U}(h:Earned m t X Y):
    Earned m t (fun n p=>M (X n p)) (fun n p=>M (Y n p)):=by
  obtain ⟨a,ap,paid⟩:=h
  refine ⟨‖M‖*a,mul_nonneg (norm_nonneg _) ap,?_⟩
  filter_upwards [paid] with p issued
  intro n top
  obtain ⟨x,y,z⟩:=issued n top
  rw [←map_sub,mul_assoc]
  exact ⟨(M.le_opNorm _).trans (mul_le_mul_of_nonneg_left x (norm_nonneg _)),
    (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left y (norm_nonneg _)),
    (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left z (norm_nonneg _))⟩

theorem joined [NormedSpace ℝ U][NormedSpace ℝ V][NormedSpace ℝ W]
    (M:U→L[ℝ]V→L[ℝ]W){X Y:ℕ→ℕ→U}{F H:ℕ→ℕ→V}(left:Earned m t X Y)(right:Earned m t F H):
    Earned m t (fun n p=>M (X n p) (F n p)) (fun n p=>M (Y n p) (H n p)):=by
  obtain ⟨a,ap,ha⟩:=left
  obtain ⟨b,bp,hb⟩:=right
  let C:=‖M‖*a*b
  have c:0≤C:=by dsimp [C];positivity
  have budget(x:U)(y:V):‖M x y‖≤‖M‖*‖x‖*‖y‖:=
    ((M x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (M.le_opNorm x) (norm_nonneg y))
  have fine(x:U)(y:V)(hx:‖x‖≤a)(hy:‖y‖≤b):‖M x y‖≤C:=(budget x y).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hx M.opNorm_nonneg) hy (norm_nonneg _) (mul_nonneg M.opNorm_nonneg ap))
  refine ⟨C+C,add_nonneg c c,?_⟩
  filter_upwards [ha,hb] with p h k
  intro n live
  obtain ⟨x,y,z⟩:=h n live
  obtain ⟨u,v,w⟩:=k n live
  refine ⟨(fine _ _ x u).trans (le_add_of_nonneg_right c),(fine _ _ y v).trans (le_add_of_nonneg_right c),?_⟩
  have first:‖M (X n p-Y n p) (F n p)‖≤C*t p:=calc
    _≤‖M‖*‖X n p-Y n p‖*‖F n p‖:=budget .. 
    _≤‖M‖*(a*t p)*b:=mul_le_mul (mul_le_mul_of_nonneg_left z M.opNorm_nonneg) u (norm_nonneg _)
      (mul_nonneg M.opNorm_nonneg ((norm_nonneg _).trans z))
    _=_:=by dsimp [C];ring
  have last:‖M (Y n p) (F n p-H n p)‖≤C*t p:=calc
    _≤‖M‖*‖Y n p‖*‖F n p-H n p‖:=budget ..
    _≤‖M‖*a*(b*t p):=mul_le_mul (mul_le_mul_of_nonneg_left y M.opNorm_nonneg) w (norm_nonneg _)
      (mul_nonneg M.opNorm_nonneg ap)
    _=_:=by dsimp [C];ring
  have split:M (X n p) (F n p)-M (Y n p) (H n p)=
      M (X n p-Y n p) (F n p)+M (Y n p) (F n p-H n p):=by simp [map_sub]
  rw [split,add_mul];exact (norm_add_le ..).trans (add_le_add first last)

end YM.Integration.WilsonMarkedIndependentMixedMomentPrice
end
