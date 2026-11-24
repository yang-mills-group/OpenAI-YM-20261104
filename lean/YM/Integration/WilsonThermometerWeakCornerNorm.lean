import YM.Integration.WilsonThermometerWeakCornerJets

/-! A uniform price for every component of a true near-position differential
with the same measured exterior held at its own locations and radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerNorm
open Filter Function Set Finset Spec Table Extraction GapsContact GapsContact.Seams Frontier6
open WilsonThermometerWeakCornerRows WilsonThermometerWeakCornerJets WilsonThermometerWeakCoordinateNorm
open PhysicalNext.Repeat.Legato
open scoped Topology Classical ContDiff BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book} (F:Final R.family f S)
variable {n:ℕ} {J:Type} [Fintype J]

private theorem relabel (f:Points n→ℂ)(x:Points n)(l:List (Points n)){k:ℕ}
    (h:l.length=k)(θ:Fin k→Points n)(stated:∀i,l.get i=θ (Fin.cast h i)):
    iteratedFDeriv ℝ l.length f x l.get = iteratedFDeriv ℝ k f x θ:=by
  subst k
  have same:l.get=θ:=by funext i; exact stated i
  rw [same]

theorem original {simple:G.Simple}{L:EveryPhase.Almanac F}(H:Roll.{u} F simple L)
    (d:Fin n→ℕ)(e:J→ℕ)(k:ℕ){s:ℝ}(sp:0<s):
    ∃(B:ℝ)(m:ℕ),1≤B ∧ ∀a∈Ioc (0:ℝ) 1,∀b∈Icc a 1,
      ∀(x:Points n)(y:J→E4),
      Pairwise (fun i j=>s*Sum.elim (fun _:Fin n=>a) (fun _:J=>b) i≤‖sites a x y i-sites a x y j‖)→
      ∀q:StateIndex F,∀(v:Fin n→S.Tag)(w:J→S.Tag),(∀i,(v i).1=d i)→(∀j,(w j).1=e j)→
        ‖iteratedFDeriv ℝ k (panel F q v w y a) x‖≤
          B*dock a^m*billSlots F a v*billSlots F b w:=by
  let A:=Fin k→Fin n×Axis
  choose B m bp wallet using fun θ:A=>exterior F H d e (List.ofFn θ) sp
  let M:ℝ:=1+∑ θ:A,B θ
  let h:=∑θ:A,m θ
  let t:ℝ:=Fintype.card A
  have tp:0≤t:=by exact Nat.cast_nonneg _
  have bp'(θ:A):0≤B θ:=zero_le_one.trans (bp θ)
  have mp:1≤M:=le_add_of_nonneg_right (Finset.sum_nonneg (fun θ _=>bp' θ))
  refine ⟨(1+t)*M,h,one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right tp) mp,?_⟩
  intro a ha b hb x y clear q v w dv dw
  have positions:Injective (sites a x y):=by
    intro i j equal
    by_contra h
    have q:=clear h
    change s * Sum.elim (fun _:Fin n=>a) (fun _:J=>b) i ≤ ‖sites a x y i-sites a x y j‖ at q
    rw [equal,sub_self,norm_zero] at q
    have rad:0<Sum.elim (fun _:Fin n=>a) (fun _:J=>b) i:=by cases i with
                                                              | inl i=>exact ha.1
                                                              | inr j=>exact ha.1.trans_le hb.1
    exact (mul_pos sp rad).not_ge q
  have pay (θ:A):‖iteratedFDeriv ℝ k (panel F q v w y a) x (fun i=>WilsonThermometerWeakCoordinateNorm.letter (θ i))‖≤
       M*dock a^h*billSlots F a v*billSlots F b w:=by
    have lit:=literal F q v w y a (fun _ hh=>smooth F q v w y a hh) (List.ofFn θ) positions
    have rd:=MSbar.Aqua.rod k (List.map WilsonThermometerWeakCoordinateNorm.letter (List.ofFn θ)) x
      ((smooth F q v w y a positions).of_le (show (k:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top))
      (by simp)
    have hrow:=wallet θ a ha b hb (fun i=>a • x i) y clear q v w dv dw
    change ‖a^(List.ofFn θ).length • panel F q (rows F (List.ofFn θ) v) w y a x‖ ≤ _ at hrow
    rw [←lit,rd] at hrow
    have rel:=relabel (panel F q v w y a) x
      (List.map WilsonThermometerWeakCoordinateNorm.letter (List.ofFn θ)) (by simp : _=k)
      (fun i=>WilsonThermometerWeakCoordinateNorm.letter (θ i)) (by intro i; simp [List.get_eq_getElem,Fin.cast])
    rw [rel] at hrow
    have Bm:B θ≤M:=(Finset.single_le_sum (f:=B) (fun _ _=>bp' _) (mem_univ θ)).trans (le_add_of_nonneg_left zero_le_one)
    have mh:m θ≤h:=Finset.single_le_sum (f:=m) (fun j _=>Nat.zero_le (m j)) (mem_univ θ)
    exact hrow.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
       (mul_le_mul Bm (pow_le_pow_right₀ (dock_valid a ha) mh) (pow_nonneg (zero_le_one.trans (dock_valid a ha)) _) (zero_le_one.trans mp))
       (billSlots_pos ..)) (billSlots_pos ..))
  have bill:0≤M*dock a^h*billSlots F a v*billSlots F b w:=by
    exact mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans mp) (pow_nonneg (zero_le_one.trans (dock_valid a ha)) _))
      (billSlots_pos ..)) (billSlots_pos ..)
  have norm:=WilsonThermometerWeakCoordinateNorm.read (iteratedFDeriv ℝ k (panel F q v w y a) x) bill pay
  calc _≤t*(M*dock a^h*billSlots F a v*billSlots F b w):=norm
       _≤(1+t)*(M*dock a^h*billSlots F a v*billSlots F b w):=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) bill
       _=_:=by ring

end YM.Integration.WilsonThermometerWeakCornerNorm
end
