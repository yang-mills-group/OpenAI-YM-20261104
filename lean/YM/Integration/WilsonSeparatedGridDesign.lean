import YM.Integration.WilsonSeparatedGridTree

/-! Choice of the real signed stencil before any physical or independent MS
field is named. At actual cutoff mesh a_j/r its leaves have true addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedGridDesign
open Filter Function Set Extraction Lattice Contacts.Mat Contacts.Sensor WilsonSeparatedBranchStencil WilsonSeparatedPhysicalRay WilsonSeparatedGridTree
open scoped Classical BigOperators
variable {n m:ℕ} {E:Type} [Fintype E]

def directions (n:ℕ) : ℝ := 1+∑ i:Fin n×Axis,‖Points.direction i.1 i.2‖
def span (n m:ℕ) (E:Type) [Fintype E] : ℝ := width n m E * directions n
def levels (n:ℕ) : ℕ := (Finset.univ:Finset (Fin n×Axis)).card
def radius (n m:ℕ) (E:Type) [Fintype E] (δ:ℝ) : ℝ := (levels n:ℝ)*(δ*span n m E)

theorem span_nonneg : 0 ≤ span n m E := by unfold span directions width;have h:0<clusterRadius (Fin n⊕E) m:=clusterRadius_pos;positivity

theorem step (X:Points n) (i:Fin n) (a:Axis) {δ:ℝ} (dp:0 ≤ δ) (t:ℝ) (ht:t∈Icc 0 (width n m E)) :
    dist (axisStep X i a δ t) X ≤ δ*span n m E := by
  have ind:‖Points.direction i a‖ ≤ directions n := by
    have each:=Finset.single_le_sum (s:=Finset.univ) (f:=fun k:Fin n×Axis=>‖Points.direction k.1 k.2‖)
      (fun k _=>norm_nonneg _) (Finset.mem_univ (i,a))
    exact each.trans (by unfold directions;linarith)
  rw [dist_eq_norm,axisStep,add_sub_cancel_left,norm_smul,norm_smul,Real.norm_of_nonneg ht.1,Real.norm_of_nonneg dp]
  have bound:=mul_le_mul ht.2 (mul_le_mul_of_nonneg_left ind dp) (mul_nonneg dp (norm_nonneg _)) (ht.1.trans ht.2)
  exact bound.trans_eq (by unfold span;ring)

def Valid (m:ℕ) (ref:E → E4) (δ:ℝ) (X:Points n) (T:Trial n) : Prop :=
  (∀ z:T.sample,Ties (fun j=>T.site z j) ref ∅ δ ∧ dist (T.site z) X ≤ radius n m E δ) ∧
  bill T ≤ (total n m E)^levels n ∧
  ∀ field:Points n → ℂ,∀ L:ℝ,0 ≤ L  → 
    (∀ Y:Points n,dist Y X ≤ radius n m E δ  →  ∀ i a,∀ U:Nodes m (width n m E),
      ‖field Y - ∑ j,bleed U.v j • field (axisStep Y i a δ (U.v j))‖ ≤ L)  → 
    ‖field X - read T field‖ ≤ L*(1+total n m E)^levels n

theorem found (m:ℕ) (ref:E → E4) {δ:ℝ} (dp:0<δ) (X:Points n) : ∃ T:Trial n,Valid m ref δ X T :=
  enrolled m ref dp (δ*span n m E) (mul_nonneg dp.le span_nonneg) (fun Y i a=>step Y i a dp.le)
    Finset.univ X (Ties.from (fun i=>X i) ref δ)

def sold (m:ℕ) (ref:E → E4) {δ:ℝ} (dp:0<δ) (X:Points n) : Trial n := Classical.choose (found m ref dp X)

theorem checked (m:ℕ) (ref:E → E4) {δ:ℝ} (dp:0<δ) (X:Points n) : Valid m ref δ X (sold m ref dp X) :=
  Classical.choose_spec (found m ref dp X)

theorem actual (S:Schedule) (j m:ℕ) (ref:E → E4) {r:ℝ} (rp:0<r) (X:Points n)
    (z:(sold m ref (div_pos (S.a_pos j) rp) X).sample) :
    ∃ x:Fin n → Cover, RG17.posed r ((sold m ref (div_pos (S.a_pos j) rp) X).site z)=S.gridPoint j ∘ x := by
  let T:=sold m ref (div_pos (S.a_pos j) rp) X
  have ties:=(checked m ref (div_pos (S.a_pos j) rp) X).1 z |>.1
  choose addr h using fun (i:Fin n) (a:Axis)=>ties.theirs a i (by simp)
  refine ⟨addr,funext fun i=>PiLp.ext fun a=>?_⟩
  change r*(T.site z i a)=S.a j*(addr i a:ℝ)
  have coord:=h i a
  change T.site z i a=S.a j/r*(addr i a:ℝ) at coord
  rw [coord]; field_simp

end YM.Integration.WilsonSeparatedGridDesign
