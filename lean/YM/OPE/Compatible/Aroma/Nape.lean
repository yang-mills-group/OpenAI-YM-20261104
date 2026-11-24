import YM.OPE.Compatible.Aroma.Heft
/-! # Pole derivative from the divergence. Characterizes one-leg free null. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier Precision
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W T:Type*} {G:Gauge}
namespace Script
open Page
lemma wardInset (A:Labels.Taylor G n)(f:Fin n→E4)(b:Axis) (u:G.ColorIndex)(k:Axis):
    (∑ j:TypeFace 2, left ℝ 1 k j (Exterior.coord b)* takeCurl A (plaqEquiv.symm j).val.1 (plaqEquiv.symm j).val.2 f u) = takeCurl A k b f u:=by
       let x(p:PlaqAxes):=takeCurl A p.val.1 p.val.2 f u; let F i:=x (plaqEquiv.symm i); change (∑ i,left ℝ 1 k i (coord b)* F i)=_
       rw [← Equiv.sum_comp plaqEquiv]; simp_rw [show ∀ i:PlaqAxes,F (plaqEquiv i)=x i from fun i=>congr_arg x (plaqEquiv.symm_apply_apply i),plaq_map,plank]; rcases lt_trichotomy k b with h|h|h
       · let p:PlaqAxes:=⟨(k,b),h⟩; have he(p':PlaqAxes): ¬ (k=p'.val.2∧ b=p'.val.1):=by rintro ⟨a,B⟩; exact lt_asymm h (B ▸ a ▸ p'.property)
         rw [sum_eq_single p]; rw [if_pos ⟨rfl,rfl⟩,one_mul]
         · intro b _ hb; rw [if_neg (fun h=>hb (Subtype.ext (Prod.ext h.1.symm h.2.symm))),if_neg (he _),zero_mul]
         simp
       · subst b; have hu: takeCurl A k k=0:=by simp [takeCurl]
         rw [hu]; change _=0; apply sum_eq_zero; intro i _; rw [if_neg (fun h=>i.property.ne (h.1.symm.trans h.2)), if_neg (fun h=>i.property.ne (h.2.symm.trans h.1)),zero_mul]
       let p:PlaqAxes:=⟨(b,k),h⟩; have he(p':PlaqAxes):¬ (k=p'.val.1∧b=p'.val.2):=by rintro ⟨a,B⟩; exact lt_asymm h (a ▸ B ▸ p'.property)
       rw [sum_eq_single p,if_neg (he _),if_pos ⟨rfl,rfl⟩,neg_one_mul,(closedCurl A).antisymmetric k b];rfl
       · intro c _ hc; rw [if_neg (he _),if_neg (fun h=>hc (Subtype.ext (Prod.ext h.2.symm h.1.symm))),zero_mul]
       simp
-- equation indicator tensor
def flame (A: Labels.Taylor G (n+1))(b: Axis): Tensor.T E4 G.Color n:= ∑ k:Axis, (takeCurl A k b).curryLeft (basis k)
lemma flame_eq (A: Labels.Taylor G (n+1))(b:Axis)(x:E4):((n+1:ℕ):ℝ) • Tensor.diagonal (flame A b) x=∑ k:Axis,grad k (Tensor.diagonal (takeCurl A k b)) x:=by
    unfold grad Analysis.D flame Tensor.diagonal; rw [_root_.sum_apply, Finset.smul_sum]; exact sum_congr rfl fun k _=> by erw [differential_diagonal (takeCurl A k b) ((closedCurl A).coeffSym _ _), Nat.cast_smul_eq_nsmul]
lemma candle (H:FreeResolvent.FaceRow)(h:Whole H)(hp:H.read 0=1)(A: Labels.Taylor G (n+1))(p: Fin n→Axis)(x:Cover)(a:Axis)(i:G.ColorIndex): roamsX p (meetsX (barrage H) (shadew i (ledge A.val))) (x, Exterior.coord a)= - (((n+1).factorial:ℝ)*flame A a (basis∘p) i):=by
   let t:= shadew i (ledge A.val); have he(k: Axis):
      let j:= Fin.cons k p
      roamsX j (meetsX (cobound 1) t)=fun x:Cover × TypeFace 2=>((n+1).factorial:ℝ)*takeCurl A (plaqEquiv.symm x.2).val.1 (plaqEquiv.symm x.2).val.2 (basis∘j) i:=by
       intro j; ext1 x; refine (Eq.trans ?_ (poiseMark i _ j x.1 (plaqEquiv.symm x.2))); rw [show plaquette (plaqEquiv.symm x.2)=x.2 from plaqEquiv.apply_symm_apply x.2]
   change roamsX p (meetsX (barrage H) t) _=_; rw [peck h _ (show Quiet t ((n+1)+1) from quietShade (low_quiet (ledgeL _)) _)]; apply congr_arg Neg.neg; unfold flame
   change _= ((n+1).factorial:ℝ)* chin i ((∑ k,(takeCurl A k a).curryLeft (basis k)) _); rw [_root_.sum_apply,map_sum,Finset.mul_sum]
   apply sum_congr rfl; intro k _; simp_rw [he]; erw [axis_mem H h hp (fun (x:TypeFace 2)=> ((n+1).factorial:ℝ)*takeCurl A (plaqEquiv.symm x).val.1 (plaqEquiv.symm x).val.2 (basis∘Fin.cons k p) i)]; simp_rw [mul_left_comm (left ℝ _ k _ _),← Finset.mul_sum]; rw [wardInset]; congr 1; rw [show basis ∘ Fin.cons k p= Fin.cons (basis k) (basis∘p) from funext fun j=>by refine Fin.cases ?_ (fun i=>?_) j<;>rfl]; rfl
lemma candleLow (H:FreeResolvent.FaceRow)(h:Whole H) {v:fieldX (Shade G)}(hp:Low v d')(g:d'<m+2)(i:G.ColorIndex)(p: Fin m→Axis)(x:Cover)(a:Axis): roamsX p (meetsX (barrage H) (shadew i v)) (x,coord a)=0:=by
    rw [peck h p (quietShade (low_quiet hp) i)]; simp_rw [orchid hp (Nat.le_of_lt_succ g)]; simp [meetsX]
end Script
end YM.OPE.Flume
