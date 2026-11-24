import YM.Integration.WilsonSeparatedBranchStencil
import YM.Integration.WilsonSeparatedPhysicalRay

/-! The original coordinate-by-coordinate tie-safe tree. Every final node is
actually on the declared common mesh and the whole signed portfolio is chosen
before the tested correlation, including all remote insertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedGridTree
open Filter Function Set Contacts.Mat Contacts.Sensor WilsonSeparatedBranchStencil WilsonSeparatedPhysicalRay
open scoped BigOperators Classical
variable {n m:ℕ} {E:Type} [Fintype E]

def width (n m:ℕ) (E:Type) [Fintype E] : ℝ := clusterRadius (Fin n⊕E) m
def total (n m:ℕ) (E:Type) [Fintype E] : ℝ := ((m+1:ℕ):ℝ)*(width n m E)^m

theorem total_nonneg : 0 ≤ total n m E := by unfold total width;have pos:0<clusterRadius (Fin n⊕E) m:=clusterRadius_pos;positivity

theorem shifted (X:Points n) (i:Fin n) (a:Axis) (δ t:ℝ) :
    (fun j=>axisStep X i a δ t j)=pushed (fun j=>X j) i (δ • basis a) t := by
  funext j;by_cases h:j=i
  · subst j;simp [axisStep,Points.direction,pushed]
  · simp [axisStep,Points.direction,pushed,h]

/-- The leaf prices and positions, and the signed error for every trial
experiment. The radius accounts for all preceding coordinate placements. -/
theorem enrolled (m:ℕ) (ref:E → E4) {δ:ℝ} (dp:0<δ) (step:ℝ) (sp:0 ≤ step)
    (reach:∀ X:Points n,∀ i a,∀ t∈Icc 0 (width n m E),dist (axisStep X i a δ t) X ≤ step)
    (s:Finset (Fin n×Axis)) (X:Points n) (ties:Ties (fun j=>X j) ref s δ) :
    ∃ T:Trial n,
      (∀ z:T.sample,Ties (fun j=>T.site z j) ref ∅ δ ∧ dist (T.site z) X ≤ (s.card:ℝ)*step) ∧
      bill T ≤ (total n m E)^s.card ∧
      ∀ field:Points n → ℂ,∀ L:ℝ,0 ≤ L → 
        (∀ Y:Points n,dist Y X ≤ (s.card:ℝ)*step → ∀ i a,∀ U:Nodes m (width n m E),
          ‖field Y-∑ j,bleed U.v j • field (axisStep Y i a δ (U.v j))‖ ≤ L) → 
        ‖field X-read T field‖ ≤ L*(1+total n m E)^s.card := by
  induction s using Finset.induction_on generalizing X with
  | empty=>
    refine ⟨single X,fun z=>⟨ties,by simp [single]⟩,by simp [bill_single],?_⟩
    intro field L lp _;simp [read_single,lp]
  | @insert key s apart ih=>
    rcases key with ⟨i,a⟩
    obtain ⟨U,place⟩:=Ties.successor (fun j=>X j) ref δ dp i a m
    let Z (j:Fin (m+1)):=axisStep X i a δ (U.v j)
    have landing (j):Ties (fun k=>Z j k) ref s δ:=by
      dsimp only [Z];rw [shifted];exact place s apart ties j
    choose child located costs price using fun j=>ih (Z j) (landing j)
    have within (j:Fin (m+1)) (Y:Points n) (hy:dist Y (Z j) ≤ (s.card:ℝ)*step) :
        dist Y X  ≤  ((insert (i,a) s).card:ℝ)*step := by
      calc
        _ ≤ dist Y (Z j)+dist (Z j) X:=dist_triangle .. 
        _ ≤ (s.card:ℝ)*step+step:=add_le_add hy (reach X i a (U.v j) (U.starts j))
        _=_:=by rw [Finset.card_insert_of_notMem apart,Nat.cast_add_one];ring
    refine ⟨branch U child,?_,?_,?_⟩
    · intro z
      change Ties (fun j=>(child z.1).site z.2 j) ref ∅ δ ∧ _
      exact ⟨(located z.1 z.2).1,within z.1 _ (located z.1 z.2).2⟩
    · have cap:=bill_branch U child costs
      rw [Finset.card_insert_of_notMem apart,pow_succ]
      exact cap.trans_eq (mul_comm ..)
    · intro field L lpos buy
      have h0:=buy X (by rw [dist_self];positivity) i a U
      have fee (j:Fin (m+1)):‖field (Z j)-read (child j) field‖ ≤ L*(1+total n m E)^s.card :=
        price j field L lpos fun Y hy=>buy Y (within j Y hy)
      have book:=issue U (fun j=>field (Z j)) (fun j=>read (child j) field) fee
      rw [read_branch]
      calc
        _ ≤ ‖field X-∑ j,bleed U.v j • field (Z j)‖+‖(∑ j,bleed U.v j • field (Z j))-∑ j,bleed U.v j • read (child j) field‖ :=by simpa only [dist_eq_norm] using dist_triangle (field X) (∑ j,bleed U.v j • field (Z j)) (∑ j,bleed U.v j • read (child j) field)
        _ ≤ L+total n m E*(L*(1+total n m E)^s.card):=add_le_add h0 book
        _ ≤ L*(1+total n m E)^s.card+total n m E*(L*(1+total n m E)^s.card):=by
          have base:1 ≤ 1+total n m E:= by linarith only [total_nonneg (n:=n) (m:=m) (E:=E)]
          exact add_le_add ((mul_one L).symm.le.trans (mul_le_mul_of_nonneg_left (one_le_pow₀ base) lpos)) le_rfl
        _=_:=by rw [Finset.card_insert_of_notMem apart,pow_succ];ring

end YM.Integration.WilsonSeparatedGridTree
