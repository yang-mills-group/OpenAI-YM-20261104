import YM.FVA2.Orbit.Angles
/-!
# Relative determinants using the same base matrix at every point
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology Lattice PertExtension LocalH
open scoped ContDiff Topology MeasureTheory Matrix.Norms.Frobenius Classical BigOperators
section linear
variable {E F P:Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup P][NormedSpace ℝ P]

def meter (L:E≃L[ℝ] F)(M:E→L[ℝ] F):ℝ:=(M ∘L L.symm.toContinuousLinearMap).det
lemma det_comp (a b:E→L[ℝ]E) : (a ∘L b).det=a.det*b.det:= LinearMap.det_comp ..
lemma adjust (L:E≃L[ℝ] F)(M:E→L[ℝ] F) : meter L M=(L.symm.toContinuousLinearMap ∘L M).det:= by
 let e:=L.toLinearEquiv
 have hh:=LinearMap.det_conj (L.symm.toContinuousLinearMap ∘L M).toLinearMap e
 refine Eq.trans (congr_arg LinearMap.det (?_ : (M ∘L L.symm.toContinuousLinearMap).toLinearMap=e.toLinearMap ∘ₗ (L.symm.toContinuousLinearMap ∘L M).toLinearMap ∘ₗ e.symm.toLinearMap)) hh
 ext y; exact (L.apply_symm_apply _).symm
lemma cost_right (L:E≃L[ℝ] F)(M:E→L[ℝ] F)(Q:E→L[ℝ] E): meter L (M ∘L Q)=meter L M * Q.det:= by rw [adjust,adjust]; exact det_comp (L.symm.toContinuousLinearMap ∘L M) Q
lemma cost_left (L:E≃L[ℝ] F)(M:E→L[ℝ] F)(Q:F→L[ℝ] F): meter L (Q ∘L M)=Q.det * meter L M:= det_comp Q (M ∘L L.symm.toContinuousLinearMap)
@[simp] lemma meter_self (L:E≃L[ℝ] F): meter L L.toContinuousLinearMap=1:= by
 unfold meter; rw [ show L.toContinuousLinearMap ∘L L.symm.toContinuousLinearMap= ContinuousLinearMap.id ℝ _ from ContinuousLinearMap.ext (L.apply_symm_apply)]; exact map_one LinearMap.det
lemma transverse_cost (L:E≃L[ℝ] F) (V:F≃L[ℝ] P)(M:F→L[ℝ] P)(Q:E→L[ℝ] F) : meter (L.trans V) (M ∘L Q)=meter V M * meter L Q:= by
    let l:=L.toContinuousLinearMap; let m:=meter L Q; let u:= Q ∘L L.symm.toContinuousLinearMap
    change meter (L.trans V) (M ∘L Q)= _
    have he : (M ∘L Q) ∘L (L.trans V).symm.toContinuousLinearMap= (M ∘L u) ∘L V.symm.toContinuousLinearMap:= rfl
    unfold meter at *; rw [he]; exact cost_right ..

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
-- product upper triangles
lemma upper (L:E×F→L[ℝ] E×F) (M:E→L[ℝ] E)(Q:F→L[ℝ] F)(h:∀ x, L (x,0)=(M x,0))(hh:∀ y,(L (0,y)).2=Q y) : L.det=M.det * Q.det:= by
    let Ω:=Module.finBasis ℝ E; let Β:=Module.finBasis ℝ F; let v:= Ω.prod Β; let A:= ContinuousLinearMap.fst ℝ E F ∘L L ∘L ContinuousLinearMap.inr ℝ E F; let p:=LinearMap.toMatrix Ω Ω M.toLinearMap; let q:=LinearMap.toMatrix Β Β Q.toLinearMap; let H:=LinearMap.toMatrix v v L.toLinearMap
    have ht : H= Matrix.fromBlocks p (LinearMap.toMatrix Β Ω A.toLinearMap) 0 q := by
      ext (i|i) (j|j) <;> simp only [H,v,p,q,Module.Basis.prod_apply,LinearMap.toMatrix_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Module.Basis.prod_repr_inl,Module.Basis.prod_repr_inr]
      · change Ω.repr (L (_,0)).1 i = Ω.repr (M _) i; rw [h]; rfl
      · rfl
      · change Β.repr (L (_,0)).2 i=0; rw [h]; simp
      change Β.repr (L (0,_)).2 i=Β.repr (Q _) i; rw [hh]; rfl
    change LinearMap.det _=LinearMap.det _ * LinearMap.det _; rw [← LinearMap.det_toMatrix Ω, ← LinearMap.det_toMatrix Β, ←LinearMap.det_toMatrix v]; change H.det=p.det*q.det; rw [ht]; exact Matrix.det_fromBlocks_zero₂₁ ..
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma pri {v:P×E→F} {a:P}{b:E}(h:DifferentiableAt ℝ v (a,b)) : fderiv ℝ v (a,b) ∘L ContinuousLinearMap.inl ℝ P E=fderiv ℝ (fun u=> v (u,b)) a:= by
    calc
      _ = fderiv ℝ v (a,b) ∘L ((ContinuousLinearMap.id _ P).prod (0:P→L[ℝ] E)) := rfl
      _ = _ := Eq.symm ( (h.hasFDerivAt.comp (f:=fun u:P=>(u,b)) a ((hasFDerivAt_id (𝕜:=ℝ) a).prodMk (hasFDerivAt_const ..))).fderiv )
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma secd {v:P×E→F} {a:P}{b:E}(h:DifferentiableAt ℝ v (a,b)) : fderiv ℝ v (a,b) ∘L ContinuousLinearMap.inr ℝ P E=fderiv ℝ (fun u=> v (a,u)) b:= by
 exact ((h.hasFDerivAt.comp (f:=fun u:E=>(a,u)) b ((hasFDerivAt_const ..).prodMk (hasFDerivAt_id (𝕜:=ℝ) b))).fderiv).symm
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma deriv_split (v:P×E→F) {a:P}{b:E}(h:DifferentiableAt ℝ v (a,b))(x:P)(y:E): fderiv ℝ v (a,b) (x,y)= fderiv ℝ (fun u=> v (u,b)) a x + fderiv ℝ (fun u=> v (a,u)) b y := by rw [←pri h, ←secd h,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,←map_add]; refine congr_arg (fderiv ℝ v (a,b) ·) (Prod.ext ?_ ?_) <;> ((first|exact (zero_add y).symm|exact (add_zero x).symm))
omit [FiniteDimensional ℝ F] in
lemma det_map {m:WithTop ℕ∞}{w:P→E→L[ℝ] E}{x:P}(h:ContDiffAt ℝ m w x) : ContDiffAt ℝ m (fun y=> (w y).det) x:= by
 let b:= Module.finBasis ℝ E; rw [show (fun y=> (w y).det)=fun y=> (LinearMap.toMatrix b b (w y).toLinearMap).det from funext (fun v=>(LinearMap.det_toMatrix ..).symm)]
 simp_rw [Matrix.det_apply,LinearMap.toMatrix_apply]; exact ContDiffAt.sum (fun s _=> ContDiffAt.const_smul _ (contDiffAt_prod fun i _=> ( (b.coord (s i)).toContinuousLinearMap.contDiff.contDiffAt ).comp (f:=fun p=> w p (b i)) x (h.clm_apply contDiffAt_const))) -- sign
omit [FiniteDimensional ℝ E] in
lemma meter_map {m:WithTop ℕ∞}(L:E≃L[ℝ] F) {f:P→E→L[ℝ] F}{x:P}(h:ContDiffAt ℝ m f x): ContDiffAt ℝ m (fun y=> meter L (f y)) x:= det_map (h.clm_comp (f:=fun _:P=> L.symm.toContinuousLinearMap) contDiffAt_const)
end linear
end YM.FVA2.Orbit
