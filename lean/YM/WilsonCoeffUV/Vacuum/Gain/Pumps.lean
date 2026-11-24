import YM.WilsonCoeffUV.Vacuum.Gain.WindToll
/-!
# Pumps. Allows inhomogeneous rows tied to any existing leg.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {r:ℕ} {α β V :Type*} {L:Side}{s t v A B C:ℝ}

abbrev Grazing (α:Type*)(r:ℕ):= Fin r→ Cloth α
abbrev Roof (α β:Type*)(r:ℕ):= Grazing α r→ Cloth β→ℝ

def sells (L:Side)(s C:ℝ)(U:Roof α β r):Prop := 0≤C ∧ ∀ p x,∃ i:Fin r, |U p x| ≤ C*Real.exp (-s*terrain.gap (parentC L (p i).1) x.1)
lemma sells.cost {U: Roof α β r}(h:sells L s C U)(he:C≤A): sells L s A U:=by refine ⟨h.1.trans he,fun p x=>?_⟩; obtain ⟨i,hh⟩:= h.2 p x; exact ⟨i,hh.trans (mul_le_mul_of_nonneg_right he (by positivity))⟩
lemma sells.sub {U T:Roof α β r}(h:sells L s C U)(g:sells L s A T)(he:0≤s): sells L s (C+A) (U-T):=by
  refine ⟨add_nonneg h.1 g.1,fun p x=>?_⟩; obtain ⟨i,hh⟩:=h.2 p x; obtain ⟨j,hv⟩:= g.2 p x
  let w k:= terrain.gap (parentC L (p k).1) x.1
  have he u (he:w u≤w i)(hg:w u≤w j) : |(U-T) p x| ≤ (C+A)*Real.exp (-s*w u):=by
    apply (abs_sub _ _).trans; rw [add_mul]; exact add_le_add (hh.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr he) (by linarith))) h.1)) (hv.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hg) (by linarith))) g.1))
  obtain ht|ht:= le_total (w i) (w j); exact ⟨i,he i le_rfl ht⟩; exact ⟨j,he j ht le_rfl⟩

lemma spring_pt {U:ropes Cover (Co L α) β}(h:dragCup terrain s C U)(p: Cloth α)(x) : |spring L U p x|≤C*Real.exp (-s*terrain.gap (parentC L p.1) x.1):=by have he := h.2 ((panel L α).symm p) x; rw [← show _ = parentC L p.1 from (show ((panel L α).symm p).1 = _ from congr_arg Prod.fst (patchwork p))]; exact he

def owns (L:Side)(M:ropes Cover (Co L α) β)(k: Fin r): Roof α β r := fun p x=>spring L M (p k) x
lemma ownS {M:ropes Cover (Co L α) β}(h:dragCup terrain s C M)(i:Fin r): sells L s C (owns L M i):= ⟨h.1,fun p x=>⟨i, spring_pt h (p i) x⟩⟩

lemma woven (x:Grazing β r)(y:Grazing α r)(p:Fin r→ Fin r): course terrain x y ≤ soar terrain y + ∑ i,terrain.gap (y (p i)).1 (x i).1 := by
   set C:=Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
   let H i:= terrain.gap (y (p i)).1 (x i).1
   let l:=soar terrain y
   have hv i j: terrain.gap (y i).1 (y j).1 ≤ l:= leg_le terrain (Prod.fst ∘ y) i j
   have hg (i:Fin r)(j:Fin r): terrain.gap (C (.inr i)) (C (.inl j))≤ l+H j:= by
      apply (terrain.tri _ (y (p j)).1 _).trans; exact Nat.add_le_add_right (hv ..) _
   have ht i: H i≤∑ j,H j:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
   refine league_le terrain C fun i j=>?_ ; change terrain.gap (C i) (C j) ≤ l+∑ k,H k
   cases i with
   | inl i=> cases j with
             | inl j=>
               by_cases h:i=j; · simp only [h,terrain.self]; exact Nat.zero_le _
               have he : H i+H j ≤ ∑ j,H j:=by
                  apply le_trans _ (Finset.sum_le_sum_of_subset (f:=H) (Finset.subset_univ {i,j})); simp [h]
               have hx:= terrain.tri (C (.inl i)) (C (.inr (p i))) (C (.inl j)); rw [terrain.swap (C (.inl i)) (C (.inr (p i)))] at hx
               exact hx.trans ((Nat.add_le_add_left (hg (p i) j) (H i)).trans (by omega))
             | inr j=> rw [terrain.swap]; exact (hg j i).trans (Nat.add_le_add_left (ht i) _)
   | inr i=> cases j with
             | inl j=> exact (hg i j).trans (Nat.add_le_add_left (ht j) _)
             | inr j=> exact (hv i j).trans (Nat.le_add_right ..)

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

def spinJob (P:Ten V (Cloth α) r)(R:Fin r→ Roof α β r): canal Cover α β V r r:= fun x y=> (∏ i,R i y (x i)) • P y
-- evaluate without scalar docket.
def pump (P:Ten V (Cloth α) r)(R:Fin r→ Roof α β r) : Ten V (Cloth β) r:= fun x=>∑' y, spinJob P R x y

def spunk (L:Side)(P:Ten V (Cloth α) r)(R:Fin r→ Roof α β r): canal Cover (Co L α) β V r r:= fun x y=> spinJob P R x (panel L α ∘ y)
lemma windmill (P:Ten V (Cloth α) (r+1))(R:Fin (r+1)→ Roof α β (r+1))(L:Side): pump P R=worn (spunk L P R):=by
  funext x; rw [pump,← ((Equiv.refl _).arrowCongr (panel L α)).tsum_eq]; unfold worn tie; apply tsum_congr; intro i; rw [if_neg (by omega)]; rfl
lemma lead_pump (M:ropes Cover (Co L α) β)(P:Gen V (Cloth α)):
    prism M (plants L P) (r+1) = pump (P (r+1)) (owns L M) := by
    rw [windmill (L:=L),prism, plant_pt, reflectCut]; apply congr_arg (fun F=>worn F)
    funext x y; change (∏ i,M (y i) (x i)) • P (r+1) (panel L α ∘ y)= (∏ i,spring L M ((panel L α ∘ y) i) (x i)) • _
    simp only [Function.comp_apply,spring, Matrix.submatrix_apply, Equiv.symm_apply_apply]; rfl

variable {R:Fin r→ Roof α β r}{P: Ten V (Cloth α) r}
lemma spunk_cup {K:Fin r→ℝ}(h:∀ i,sells L s (K i) (R i))(he:Amber terrain t A P)(hp:0≤s)(hv:s/L.val≤t) : pairCup terrain s ((∏ i,K i)*(A*Real.exp (8*s))) (spunk L P R):=by
   have hx:0 ≤ ∏ i,K i:= Finset.prod_nonneg fun _ _=> (h _).1
   have hA:=he.1
   have hP : Amber terrain s (A*Real.exp (8*s)) (turnTen (panel L α).symm P):= gather_coast hp (he.mono hv)
   refine ⟨by positivity,fun x y=>?_⟩
   choose j hj using fun i:Fin r=> (h i).2 (panel L α ∘ y) (x i)
   simp_rw [Function.comp_apply,parent_pack] at hj
   have hy:=woven x y j
   let g i:=terrain.gap (y (j i)).1 (x i).1
   set M:=soar terrain y
   have hu : ‖∏ i,R i (panel L α ∘ y) (x i)‖ ≤ (∏ i,K i)*Real.exp (-s*∑ i,g i):= by
      rw [Real.norm_eq_abs, Finset.abs_prod]; apply (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=> hj i)).trans; rw [Finset.prod_mul_distrib, Nat.cast_sum,Finset.mul_sum,Real.exp_sum]
   rw [spunk,spinJob,norm_smul]; refine (mul_le_mul hu (hP.2 y) (norm_nonneg _) ((norm_nonneg _).trans hu)).trans ?_
   rw [mul_mul_mul_comm,←Real.exp_add,Real.exp_add]
   apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← Real.exp_add, ← mul_add]; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (by linarith)
   rw [add_comm,← Nat.cast_add]; exact_mod_cast hy
variable [Fintype α]
lemma pump_pay {P:Ten V (Cloth α) (r+1)}{R:Fin (r+1)→ Roof α β (r+1)}{K:Fin (r+1)→ℝ}(h:∀ i,sells L s (K i) (R i))(he:Amber terrain t A P)(hf:0≤v)(ht:v<s)(hv:s/L.val≤t):
     Amber terrain v (((∏ i,K i)*(A*Real.exp (8*s)))*tiePay (Co L α) (r+1) (s-v)) (pump P R):=by
   rw [windmill _ _ L]; exact worn_amber (spunk_cup h he (hf.trans ht.le) hv) hf ht
lemma pump_sum {P:Ten V (Cloth α) (r+1)}{R:Fin (r+1)→ Roof α β (r+1)}{K:Fin (r+1)→ℝ}(h:∀ i,sells L s (K i) (R i))(he:Amber terrain t A P)(hp:0<s)(hv:s/L.val≤t)(x):
    Summable fun i=> ‖spinJob P R x i‖:=by
   have H:= (tie_cost (spunk_cup h he hp.le hv) hp le_rfl x).2.1
   exact ((Equiv.refl _).arrowCongr (panel L α)).summable_iff.mp (H.congr (fun y=> by rw [tie,if_neg (by omega)]; rfl))
end YM.WilsonCoeffUV.Bank
