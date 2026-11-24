import YM.RG11Proof.Jets.Matrix
/-!
# Slot amplitudes with a distinguished first slot / tree compositorial rules

This API aligns with `insert` in PertExtension but doesn't use the sigma
position tag (algebra purely at one fixed arity and test). All real & complex
coefficients incl vacuum, not stats or connected. For n+m split via Sum etc
in subsequent files. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG11.Nodes
open YM.RG11.Jets PowerSeries
open scoped BigOperators Classical
variable {J L R M : Type*} {n:ℕ}

abbrev reading (J R:Type*) (n:ℕ):=(Fin n→J)→R
section
variable (s:Square J R)(u z: J→R)
variable [CommSemiring R][Fintype J]

def cross (i j:Fin n→J):=∏ b, s (i b) (j b)

def plant (A:reading J R n)(i:Fin n→J) := ∑ w:Fin n→J, A w * cross s i w

def fires (j:J):R:=∑ i:J, u i * s i j

def armed (A:reading J R (n+1))(i:Fin n→J):=∑ j, u j * A (Fin.cons j i)

@[simp] theorem cross_nil (i j:Fin 0→J) : cross s i j=1:=by simp [cross]
@[simp] theorem cross_next (i j:Fin n→J)(x y): cross s (Fin.cons x i) (Fin.cons y j) = (s x y)*cross s i j:=by
  unfold cross; rw [Fin.prod_univ_succ]; simp

theorem Plant.germ (A:reading J R (n+1))(i:Fin n→J)(x:J):plant s A (Fin.cons x i)=
    ∑ j,∑ w: Fin n→J,A (Fin.cons j w)*(s x j*cross s i w):=by
   unfold plant
   let Z (p:Fin (n+1)→J):=A p * cross s (Fin.cons x i) p
   let E:(Fin (n+1)→J)≃ J × (Fin n→J):={
      toFun := fun p=>(p 0,Fin.tail p)
      invFun:=fun p=>Fin.cons p.1 p.2
      left_inv:=fun i=> Fin.cons_self_tail i
      right_inv:=by rintro ⟨i,j⟩; ext <;> simp }
   rw [← Finset.sum_product'] -- implicit?
   exact Fintype.sum_equiv E Z _ (fun p=>by
     change Z p= A (Fin.cons (p 0) (Fin.tail p))*(s x (p 0)*cross s i (Fin.tail p)); unfold Z
     nth_rw 1 [← Fin.cons_self_tail p]; rw [show cross s (Fin.cons x i) p=cross s (Fin.cons x i) (Fin.cons (p 0) (Fin.tail p)) from congrArg _ (Fin.cons_self_tail p).symm,cross_next])

 theorem porch (A:reading J R (n+1))(v:Fin n→J): armed u (plant s A) v=plant s (armed (fires s u) A) v:=by
   unfold armed
   simp_rw [Plant.germ s]; unfold plant; simp only [Finset.mul_sum,fires,Finset.sum_mul]
   rw [Finset.sum_comm]; conv_rhs=>rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro w _; ring

 theorem interior (A B:reading J R n)(v:Fin n→J): plant s (A+B) v=plant s A v+plant s B v:=by simp [plant,Finset.sum_add_distrib,add_mul]

 theorem planting_total [Fintype L](A:L → reading J R n)(v:Fin n→J):
    plant s (fun i=> ∑ j:L,A j i) v=∑ j:L,plant s (A j) v:=by simp only [plant,Finset.sum_mul]; exact Finset.sum_comm

 theorem grow_linear (A:reading J R n)(r:R)(v:Fin n→J):
    plant s (fun i=>r*A i) v=r*plant s A v:=by simp [plant,Finset.mul_sum,mul_assoc]

-- zero-head s=I
@[simp] theorem plant_id (A:reading J R n)(v:Fin n→J): plant (1:Square J R) A v=A v:=by
   exact YM.PertExtension.Position.insert_one (arity:=fun _:Unit=>n) (fun i=> A i.2) (⟨(),v⟩)
@[simp] theorem fires_id (j:J): fires (1:Square J R) u j=u j:=by simp [fires,Matrix.one_apply]
 theorem plant_duo (t : Square J R)(A:reading J R n)(v:Fin n→J): plant s (plant t A) v=plant (s*t) A v:=by
   exact congrFun (YM.PertExtension.Position.insert_twice (arity:=fun _:Unit=>n) (fun i=>A i.2) (fun i j=>t i j) (fun i j=>s i j)) ⟨(),v⟩
 theorem fires_duo (t : Square J R)(j:J): fires t (fires s u) j=fires (s*t) u j:=by
   simp only [fires,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul,mul_assoc]; exact Finset.sum_comm

 theorem deposit {M:Type*}[CommSemiring M](ψ:R→+*M) (A:reading J R n)(v:Fin n→J): ψ (plant s A v)=plant (s.map ψ) (ψ ∘ A) v:=by simp [plant,cross,map_sum,map_prod]
end
section
variable [CommRing R][Fintype J]

 theorem through_plant (s:Square J (PowerSeries R)) {A B:reading J (PowerSeries R) n}{N}(h:∀ z,Through N (A z) (B z))(v:Fin n→J) : Through N (plant s A v) (plant s B v):=
   Through.sum (fun _ _=>(h _).mul (Through.refl _))

 theorem through_armed (u:J→PowerSeries R) {A B:reading J (PowerSeries R) (n+1)}{N}(h:∀z, Through N (A z) (B z))(v:Fin n→J):
    Through N (armed u A v) (armed u B v):=Through.sum (fun _ _=>(Through.refl _).mul (h _))

theorem firing_piece (D:Square J (PowerSeries R))(k:ℕ)(u:J→PowerSeries R): (fun j=>coeff k (fires D u j))=
    ∑ z∈Finset.HasAntidiagonal.antidiagonal k,fires (piece z.2 D) (fun i=>coeff z.1 (u i)) :=by
  funext j; simp only [fires,map_sum,coeff_mul,Finset.sum_apply,piece_apply]; exact Finset.sum_comm
end
end YM.RG11.Nodes
