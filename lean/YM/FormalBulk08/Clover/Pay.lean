import YM.FormalBulk08.Quire.Warrant
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Clover
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge} {K:KernelChoices}{E m n l e r j t d D R:ℕ}{X I:Type}
variable {J U:X→ℕ} {F:∀ i:X,Flight (J i) (U i)}{V:∀ i:X,Lodge (F i).patch}{τ:Time X}{σ η δ g μ:X→ℝ}
variable {o:Loc G 1}{T S:X→ Anthem D G}{Z: Frame G d}

-- payment on ALL local smoothing choices. Has ∀ G-FRAME fix. no orientation lectures vs Treasury
structure Payroll (K:KernelChoices)(Z:Frame G d)(o:Loc G 1)(F:∀ i:X,Flight (J i) (U i))(V:∀ i:X,Lodge (F i).patch)(E R D:ℕ) (τ:Time X)(σ η μ:X→ℝ) :Prop where
   width : ∀ i,0<η i
   bills : ∀ e≤ E,∀ r≤ R+E,∀ l≤R, ∃ C:X→ℝ, Soft τ C ∧ ∀ i, Office K Z o (σ i) (η i) (F i) (V i) e r l D (μ i) (C i)
   uptake : ∀ r≤ R+E,∃ C:X→ℝ,Soft τ C ∧ (∀ i,0≤C i) ∧ ∀ i,Penny Z o (η i) (C i) r
lemma label_quote {T: X→ Studio D→Tile (edgeL G) r}(w:Payroll K Z o F V E R D τ σ η μ)(i:Letter Z)(h:Tender τ o η g T)(hp:r≤R+E): Faint τ g (fun x=> pearlJ Z (T x (inside Z i D)) (mint Z i)):= by
   obtain ⟨B,b,p,H⟩:=h; obtain ⟨C,c,u,W⟩:=w.uptake r hp; let n:=‖inside Z i D‖; refine ⟨_,(c.times b).times (soft_coin τ n),fun i=>mul_nonneg (mul_nonneg (u i) (p i)) (by unfold n; positivity),fun x=>?_⟩; refine (W x|>.pays _ _ (H x _) i).trans_eq ?_; ring
lemma bill_many {g:X→ℝ}(h:∀ i,0≤g i)(A:Finset I){T:I→X→ℝ}(hp:∀ i∈ A,Faint τ g (T i)):
    ∃ B:X→ℝ,Soft τ B ∧ (∀ i,0≤B i) ∧ ∀ i∈A,∀ x,|T i x|≤ B x*g x:= by
    induction A using Finset.induction with
    | empty=> exact ⟨0,soft_coin _ _,by simp,by simp⟩
    | @insert i A ht ih=> obtain ⟨B,hB,H,Q⟩:= ih fun j hj=>hp j (Finset.mem_insert_of_mem hj); obtain ⟨C,c,t,P⟩:= hp i (Finset.mem_insert_self ..); refine ⟨_,hB.plus c,fun i=>add_nonneg (H i) (t i),fun j hj x=>?_⟩; rw [add_mul]; rcases Finset.mem_insert.mp hj with rfl|hU; exact (P x).trans (le_add_of_nonneg_left (mul_nonneg (H x) (h x))); exact (Q _ hU x).trans (le_add_of_nonneg_right (mul_nonneg (t x) (h x)))
lemma tender_many {r:I→ℕ}{T:(i:I)→ X→ Studio D→Tile (edgeL G) (r i)} (A:Finset I)(h:∀ i,0≤g i)(hp:∀ i∈A,Tender τ o σ g (T i)):
    ∃ B:X→ℝ, Soft τ B∧(∀ i,0≤B i) ∧ ∀ i∈A,∀ x p,Knoxville (fame _) (σ x) (0,o) (T i x p) ((B x*g x)*‖p‖) := by
   induction A using Finset.induction with
   | empty=> exact ⟨0,soft_coin _ _,by simp,by simp⟩
   | @insert i A ht ih=>
       obtain ⟨B,hB,H,Q⟩:= ih fun j hj=>hp j (Finset.mem_insert_of_mem hj); obtain ⟨C,c,t,P⟩:=hp i (Finset.mem_insert_self ..)
       refine ⟨_,hB.plus c,fun i=> add_nonneg (H i) (t i),fun j hj x p=>?_⟩; rw [add_mul,add_mul]; rcases Finset.mem_insert.mp hj with rfl|hU
       · rw [mul_assoc (C x)]; exact (P x p).mono (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (H x) (h x)) (norm_nonneg _)))
       exact (Q _ hU _ _).mono (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (t x) (h x)) (norm_nonneg _)))
lemma faint_sums {f:I→ X→ℝ} (U:Finset I)(h:∀ i∈U,Faint τ g (f i)) : Faint τ g (fun x=>∑ i∈U,f i x):= by
    induction U using Finset.induction with
    | empty=>simp only [Finset.sum_empty]; exact faint_zero ..
    | @insert i V hi ih=>simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma Prefix_role (Z:Frame G d) (h:∀ x,Clef o (T x) l)(hx:∀ j:Letter Z,Faint τ g (fun i=> coeff e (echo Z (T i) j)))(hp:∀ k m:ℕ, k<e→ m≤ l+k → Tender τ o σ g (fun i p=>T i p k m))(hs:∀ x,0≤ g x):
    ∃ B:X→ℝ,Soft τ B ∧ (∀ i,0≤ B i) ∧ (∀ i,Deposit o (σ i) (T i) e (B i*g i)) ∧ ∀ i:Letter Z,∀ j, ‖coeff e (echo Z (T j) i)‖ ≤ B j*g j:= by
   let U:= (Finset.range e ×ˢ Finset.range (l+e+1)).filter (fun i=> i.2≤l+i.1)
   obtain ⟨B,b,P,H⟩:= tender_many U hs (fun i hi=> hp _ _ (Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1) (Finset.mem_filter.mp hi).2); obtain ⟨A,a,W,Q⟩:=bill_many hs Finset.univ (fun j _=>hx j)
   have hv i:0≤B i+A i:= add_nonneg (P i) (W i); refine ⟨_, b.plus a,hv,fun i=>?_,fun i k=>?_⟩
   · have ht:=mul_nonneg (hv i) (hs i); refine ⟨ht,fun j hj m p=>?_⟩; by_cases he:m≤l+j
     · rw [add_mul,add_mul]; exact (H (j,m) (by unfold U;simp;omega) i p).mono (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (W i) (hs i)) (norm_nonneg _)))
     rw [show T i p j m=0 from Classical.byContradiction fun ht=> he ((h i).fare.1 p j m ht)]; exact (Knox_zeros _).mono (mul_nonneg ht (norm_nonneg _))
   rw [add_mul]; exact (Q i (Finset.mem_univ _) k).trans (le_add_of_nonneg_left (mul_nonneg (P k) (hs k)))
end YM.FormalBulk08.Clover
