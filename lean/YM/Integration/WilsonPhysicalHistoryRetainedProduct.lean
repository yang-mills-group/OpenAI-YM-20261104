import YM.Integration.WilsonPhysicalHistoryRetainedVertices

/-! Telescope the entire signed product of one original Mayer molecule on
its own affine sample. Each summand inserts exactly one changed regular
letter and retains all of the other actual partner values. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Bloch Laurent Push Push.AbsoluteSums Precision Exterior Shell Channel
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side}

private theorem signed_list {ι : Type*} (f g : ι→ℝ) (s : List ι) :
    (s.map f).prod-(s.map g).prod = ∑ k : Fin s.length,
      (f (s.get k)-g (s.get k))*((s.take k.val).map g).prod*
        ((s.drop (k.val+1)).map f).prod := by
  induction s with
  | nil => simp
  | cons i s ih =>
    let t : Fin (s.length+1)→ℝ := fun k=>(f ((i::s).get k)-g ((i::s).get k))*
      (((i::s).take k.val).map g).prod*(((i::s).drop (k.val+1)).map f).prod
    change ((i::s).map f).prod-((i::s).map g).prod=∑ k : Fin (s.length+1),t k
    rw [Fin.sum_univ_succ (f:=t)]
    dsimp only [t]
    simp only [List.map_cons,List.prod_cons,Fin.val_zero,List.take_zero,List.map_nil,List.prod_nil,
      mul_one,Fin.val_succ,List.take_succ_cons,List.drop_succ_cons,List.drop_zero,
      List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ] at *
    have scale : (∑ k : Fin s.length,(f s[k.val]-g s[k.val])*
        (g i*((s.take k.val).map g).prod)*((s.drop (k.val+1)).map f).prod) =
        g i*((s.map f).prod-(s.map g).prod) := by
      rw [ih,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [scale]
    ring

def regularFee (S : StepData c f) (b : ℕ→ℝ) : Head S→ℝ
  | .inr (.inr (.inl (.inl (.inl i)))) => b i
  | _ => 0

private theorem individual {S : StepData c f} (a b : Head S→ℝ) (r : ℕ→ℝ)
    (changed : ∀ i,|a (regularHead S i)-b (regularHead S i)| ≤ (5/2:ℝ)*r i)
    (same : ∀ v,(∀ i : ℕ,v≠regularHead S i)→a v=b v) (v : Head S) :
    |a v-b v|≤(5/2:ℝ)*regularFee S r v := by
  by_cases h : ∃ i,v=regularHead S i
  · obtain ⟨i,rfl⟩:=h
    exact changed i
  · rw [same v (fun i eq=>h ⟨i,eq⟩),sub_self,abs_zero]
    rcases v with _|_|((i|_)|_)|_ 
    all_goals first | exact (h ⟨i,rfl⟩).elim | norm_num [regularFee]

theorem molecule_product (R : Run G) {N n j d : ℕ} (hj : j<N) (A : Comparison R (p:=n) hj d) :
    let P:=R.family.path.rep N n j
    let Q:=approximation R (p:=n) hj d
    let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)
    ∃ b : ℕ→ℝ, (∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
      P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
      ∀ {c : Side} {S : StepData c (R.family.side j n)} {T : Tube G S} {F : Forest S.ratio}
        (X : Coat T F) (C : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ)
        (z : Air (R.family.side j n) G) (p : Molecule S),
        let v:=X.vertex P C W a l m z
        let u:=X.vertex Q C W a l m z
        let s:=p.toList
        let other := fun k : Fin s.length=>((s.take k.val).map u).prod*((s.drop (k.val+1)).map v).prod
        (X.term P C W a l m z p-X.term Q C W a l m z p =
          ∑ k : Fin s.length,(v (s.get k)-u (s.get k))*other k) ∧
        (δ≤1 → (∀ i : ℕ,|v (regularHead S i)|≤1/4) →
          |X.term P C W a l m z p-X.term Q C W a l m z p| ≤
            ∑ k : Fin s.length, (5/2:ℝ)*regularFee S b (s.get k)*|other k|) := by
  dsimp only
  obtain ⟨b,pay,rows⟩:=molecule_rows R hj A
  refine ⟨b,pay,?_⟩
  intro c S T F X C W a l m z p
  let P:=R.family.path.rep N n j
  let Q:=approximation R (p:=n) hj d
  let v:=X.vertex P C W a l m z
  let u:=X.vertex Q C W a l m z
  let s:=p.toList
  let others (k : Fin s.length):=((s.take k.val).map u).prod*((s.drop (k.val+1)).map v).prod
  have eq : X.term P C W a l m z p-X.term Q C W a l m z p =
      ∑ k : Fin s.length,(v (s.get k)-u (s.get k))*others k := by
    simpa only [s,v,u,others,Finset.prod_map_toList,Coat.term,mul_assoc] using signed_list v u s
  refine ⟨eq,?_⟩
  intro hsmall quarter
  rw [eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg (others k))
  apply individual v u b _ (rows X C W a l m z).2
  intro i
  refine ((rows X C W a l m z).1 i hsmall).trans ?_
  have nn : 0 ≤ b i := by
    exact nonneg_of_mul_nonneg_right ((abs_nonneg _).trans ((rows X C W a l m z).1 i hsmall)) (by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith only [quarter i]) nn

end YM.Integration.OriginalMarkedRunAction
