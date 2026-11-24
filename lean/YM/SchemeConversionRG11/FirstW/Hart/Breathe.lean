import YM.SchemeConversionRG11.FirstW.Hart.Skin
/-! All lattice polynomial pure-gauge shifts from an exact primitive, on the test polynomial space. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Lattice Pert Align Topology Maxwell Filter MultiNext.SignedSource
open scoped BigOperators Classical
variable {G : Gauge} {X : Type*} [One X] [AddCommGroup X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def degreeNext (k : ℕ) (f:Axis → Cover→ E) (z : E4) := ((k:ℝ)+1)⁻¹ • ∑ i:Axis,z i • Newt.piece k (f i) (z-basis i)
lemma closed_diag (f : Wind G ℤ) (hf : quietly f) (i j:Axis) : Newt.jump (field4 i f) j=Newt.jump (field4 j f) i := by
  funext x
  have he:=hf j i x; unfold Bare.wideCurl at he; unfold Newt.jump field4; apply sub_eq_zero.mp; rw [←he]; abel
lemma agrees (k : ℕ) (f : Axis→ Cover→ E) (h : ∀ i j, Newt.jump (f i) j=Newt.jump (f j) i) (x : E4) (j : Axis) :
   degreeNext k f (x+basis j)-degreeNext k f x=Newt.piece k (f j) x := by
  cases k with
  | zero=> simp only [degreeNext, Newt.piece,PiLp.add_apply,add_smul,Finset.sum_add_distrib]; simp [basis,ite_smul]
  | succ k=>
    let b:= ((k:ℝ)+1); have hb : 0<b:=by unfold b; positivity
    let A (x:E4) (i : Axis) := Newt.piece (k+1) (f i) (x-basis i)
    let R:=Newt.piece (k+1) (f j) x
    have h0 : ∑ i:Axis,(basis j) i • A (x+basis j) i= R := by simp [A,R,basis,ite_smul]
    have h1 : (∑ i:Axis,x i • A (x+basis j) i) - ∑ i:Axis,x i • A x i = ∑ i:Axis,x i • Newt.piece k (Newt.jump (f j) i) (x-basis i) := by rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a _; rw [←smul_sub]; unfold A; rw [show x+basis j-basis a=x-basis a+basis j by abel,Newt.ix,h a j]
    have h2 : b • R = ∑ i:Axis,x i • Newt.piece k (Newt.jump (f j) i) (x-basis i) := by unfold R; rw [Newt.piece]; exact smul_inv_smul₀ hb.ne' _
    unfold degreeNext; rw [← smul_sub]; simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib,Nat.cast_add,Nat.cast_one];
    change (b+1)⁻¹ • ((∑ i:Axis,x i • A (x+basis j) i)+(∑ i:Axis, (basis j) i • A (x+basis j) i)-(∑ i:Axis,x i• A x i))=R
    rw [h0,add_sub_right_comm,h1,←h2,show b • R + R=(b+1) • R from by simp only [b,add_smul,one_smul],inv_smul_smul₀ (by positivity : b+1≠0)]
lemma primitive (f : Field4 G) (k : ℕ) (h : f ∈ stor G k) (hf : quietly f) : ∃ u : Cover→ G.Color, u 0=0 ∧ momentE u=f ∧ u∈Loft G.Color (k+1) := by
  let q i:=field4 i f; let M := Finset.range (k+1)
  let E x:= -(∑ i∈M,degreeNext i q (Pattern.xyz x))
  have he j x : E x - E (x+step j) = q j x := by
    unfold E; rw [neg_sub_neg, ←Finset.sum_sub_distrib, Pattern.xyz_step]; simp_rw [agrees _ q (closed_diag f hf)]; exact Eq.symm (sub_eq_zero.mp (congrFun (loft_tail (stor_mem.mp h j)) x))
  have hD:E∈Loft G.Color (k+1) := by
    rintro (_|⟨j,b⟩) H; · simp at H
    rw [combine,←combine_up,show up j E= -(q j) from funext fun x=> by rw [up,← neg_sub (E x),he];rfl]
    rw [show -(q j)=0-q j by simp, combine_sub, combine_zero,stor_mem.mp h j b (by rw [List.length_cons] at H; omega),sub_self]
  refine ⟨E,?_,funext (fun i=>he ..),hD⟩; simp [E,degreeNext,Pattern.xyz]
end YM.RG11.FirstW
