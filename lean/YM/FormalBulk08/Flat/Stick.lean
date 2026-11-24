import YM.FormalBulk08.Flat.Copse

/-!
Repackage linear finite stencils as period-uniform Row.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f} {j : ℕ} {α β : Type}

abbrev Stick (β : Type) := (Cover × β) →₀ ℝ

def deposit (V : α → Stick β) : Row α β := fun i j k=> V i (k,j)

def tollHere [Fintype β] (x : Site c) (v : Co c β→ℝ) : Stick β →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ (fun y=> v (x+wrap c y.1,y.2))

lemma stick_eval [Fintype β] (V : α→Stick β) (x : Site c) (i) (v : Co c β→ℝ) :
    ((deposit V).acts c*ᵥ v) (x,i)=tollHere x v (V i) := by
  let r:=V i; classical
  change (∑ k : Co c β, (∑' z : Cover, if k.1=x+wrap c z then r (z,k.2) else 0)*v k)=tollHere x v r
  generalize r = f
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    have he (k : Co c β) (t : Stick β) : Summable (fun z : Cover=> if k.1=x+wrap c z then t (z,k.2) else 0) := by
      apply summable_of_ne_finset_zero (s:=t.support.image Prod.fst)
      intro z hz; split; swap; · rfl
      exact Finsupp.notMem_support_iff.mp (fun h=> hz (Finset.mem_image_of_mem _ h))
    have hs (k : Co c β) : (∑' z : Cover, if k.1=x+wrap c z then (p+q) (z,k.2) else 0) =
      (∑' z : Cover, if k.1=x+wrap c z then p (z,k.2) else 0)+(∑' z : Cover, if k.1=x+wrap c z then q (z,k.2) else 0) := by
      rw [← (he k p).tsum_add (he k q)]; refine tsum_congr fun i => ?_; split <;> simp [*]
    simp_rw [hs,add_mul]; rw [Finset.sum_add_distrib,hp,hq,map_add]
  | single b r =>
    have hx (j : Co c β) : (∑' z : Cover,if j.1=x+wrap c z then Finsupp.single b r (z,j.2) else 0) = if j=(x+wrap c b.1,b.2) then r else 0 := by
      rcases b with ⟨a,b⟩; rcases j with ⟨y,k⟩
      rw [tsum_eq_single a]
      · by_cases h:y=x+wrap c a <;> by_cases hh : k=b <;> simp [h,hh,Ne.symm]
      intro w hw; simp [Ne.symm hw]
    simp_rw [hx]; simp [tollHere,ite_mul]

lemma deposit_price [Fintype α] [Fintype β] (V : α→Stick β) (η : ℝ) : ∃ C : ℝ,0<C ∧ (deposit V).strip η C := by
  classical
  have H (x : α×β) : ∃ C : ℝ, 0<C ∧ Laurent.Width η C (deposit V x.1 x.2) := by
    let v:=deposit V x.1 x.2
    let q (k : Cover) := Real.exp (η*Laurent.size k)*‖v k‖
    have hq k : 0≤q k:=by unfold q; positivity
    have ht : Summable q := by
      apply summable_of_ne_finset_zero (s:=(V x.1).support.image Prod.fst)
      intro i hi; have hx : v i=0 := Finsupp.notMem_support_iff.mp (fun h=>hi (Finset.mem_image_of_mem _ h))
      simp [q,hx]
    exact ⟨(∑' i,q i)+1,by have : 0≤∑' i,q i := tsum_nonneg hq; linarith,hq,ht,by change (∑' i,q i)≤_; linarith⟩
  choose C hC hc using H
  refine ⟨1+∑ i,C i,lt_add_of_pos_of_le (b:=0) one_pos (Finset.sum_nonneg (fun i _=> (hC i).le)),fun i j=>?_⟩ -- lt
  exact (hc (i,j)).mono le_rfl ((Finset.single_le_sum (f:=C) (fun i _=> (hC i).le) (Finset.mem_univ (i,j))).trans (by linarith))

/-- Bond relative to coarse reference cell, from cover point in fine units. -/
def boxCoord (P : Patch) (z : Cover) := (Stationary.rent P.L z,wrap P.L z)
def nextCoord (G : Gauge) (P : Patch) (b : Edge Cover) (i : G.ColorIndex) : Cover × (Co P.L (Loc G 1)) :=
    ((boxCoord P b.1).1, (boxCoord P b.1).2, coord b.2,i)

/-- Explicit linear stencil for a path integral in fine cells. -/
def stride (G : Gauge) (P : Patch) (x : Cover) (k : G.ColorIndex) (s : Walk) : Stick (Co P.L (Loc G 1)) := match s with
| [] => 0
| d::l => Finsupp.single (nextCoord G P (d.used x) k) (if d.neg then -1 else 1) + stride G P (x+d.vec) k l

def stretch (S : StepData c f) (u : Site c) (x : Cover) := wrap f x+S.ratio.embed u
lemma spread_point (S : StepData c f) (u : Site c) (x : Cover) : let z:=stretch S u x
    S.ratio.parent z=u+wrap c (boxCoord S.patch x).1 ∧ S.ratio.residue z=(boxCoord S.patch x).2 := by
  intro z
  unfold z stretch
  rw [Stationary.sewn S, S.ratio.assemble_parent, S.ratio.assemble_res]; exact ⟨add_comm ..,rfl⟩
lemma spread_vec (S : StepData c f) (u : Site c) (x : Cover) (d : Step) :
    stretch S u (x+d.vec) = stretch S u x+d.vec := by unfold stretch; rw [map_add,wrap_vec]; abel
lemma spread_edge (S : StepData c f) (u : Site c) (x : Cover) (d : Step) :
    (d.used (stretch S u x))=(stretch S u (d.used x).1,(d.used x).2) := by
  rcases d with ⟨a,h|h⟩; · rfl
  simp [Step.used,stretch]; abel

lemma line_seen (S : StepData c f) (x : Site c) (o : Cover) (s : Walk) (k : G.ColorIndex) (v : Co c (Co S.patch.L (Loc G 1))→ℝ) :
    tollHere x v (stride G S.patch o k s)=integralLink (stretch S x o) s (atPaint (v ∘ unitSplit G S 1) k) := by
  induction s generalizing o with
  | nil => rw [stride,map_zero]; rfl
  | cons a s ih =>
    rw [stride,map_add,tollHere,Finsupp.linearCombination_single]
    -- unwind path once
    change _+tollHere _ _ _=(if a.neg then -_ else _)+integralLink _ _ _
    rw [ih,spread_vec S]
    congr 1
    rw [spread_edge S]; obtain ⟨hz,h⟩:= spread_point S x (a.used o).1
    split <;> simp [boxCoord,nextCoord,atPaint,unitSplit,split_co,h,hz] <;> rfl
end YM.FormalBulk08.Flat
