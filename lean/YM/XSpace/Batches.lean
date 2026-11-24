import YM.XSpace.BareProfiles
import YM.XSpace.Choices
/-!
# Regulator arrays reannounced. Coefficient by coefficient of the
formal sum on observables through each finite horizon, all linear.
Use common unit report and fixed varying weights. Nested at each regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory Taylor
open TestBudget Expense
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ}

variable (D : Initialize G) (g : Mesh)

private def pre (d j:ℕ) (p: Fin n→ℕ): Test n→ₗ[ℂ] MultilinearMap ℂ (fun _:Fin n=>Sec G d) ℂ where
  toFun t:= (PowerSeries.coeff j).compMultilinearMap ((D.report g p t).compLinearMap fun i=> part d (p i))
  map_add' t u:=by ext1 w; change PowerSeries.coeff j ((D.report g p (t+u)) _)=_+_; rw [map_add, add_apply,map_add]; rfl
  map_smul' a t:=by ext1 w; change PowerSeries.coeff j ((D.report g p (a • t)) _)= a • _; rw [map_smul, smul_apply,map_smul]; rfl

def batch (d j:ℕ): Prediction G d:= fun n=> ∑ p:Fin n→ Fin (d+1), pre D g d j fun i=> (p i).val
lemma batches (p:Fin n→Sec G d) (t:Test n) (j:ℕ): batch D g d j n t p=∑ a : Fin n → Fin (d+1), PowerSeries.coeff j ((D.report g (fun i=> (a i).val) t) (fun i=>part d _ (p i))) := by simp only [batch,LinearMap.sum_apply,sum_apply]; rfl
abbrev in_grade {E:Type} [AddCommMonoid E] [Module ℂ E] (P : MultilinearMap ℂ (fun _ : Fin n=> Sec G d) E)
    (L: Fin n→ Fin (d+1)) (p : ∀ i, On.Grade G (L i)):= P fun i=> en (show (L i).val≤d from Nat.lt_add_one_iff.mp (L i).isLt) (p i)
lemma indicated {L: Fin n→ Fin (d+1)} (p : ∀ i, On.Grade G (L i)) (t:Test n) (j:ℕ): in_grade (batch D g d j n t) L p= PowerSeries.coeff j ((D.report g (fun i=>(L i).val) t) p):=by
  rw [in_grade,batches,Finset.sum_eq_single_of_mem L (Finset.mem_univ _)]; simp only [part_same]; intro a _ ha; obtain ⟨i,hi⟩:= Function.ne_iff.mp ha; rw [MultilinearMap.map_coord_zero (i:=i) _ (part_other _ (fun h=>hi (Fin.ext h)) _), map_zero]
private lemma upper {a:ℕ} {L:Fin n→ℕ} (p : ∀ i,On.Grade G (L i)) (h:∀ i,L i≤a) (t:Test n) (j:ℕ): batch D g a j n t (fun i=> en (h i) (p i))= PowerSeries.coeff j ((D.report g L t) p):= indicated D g (L:=fun i=>⟨L i,Nat.lt_add_one_iff.mpr (h i)⟩) p t j

omit D g in
lemma calls {E:Type*} [AddCommMonoid E] [Module ℂ E] (P: MultilinearMap ℂ (fun _ : Fin n=>Sec G d) E) (w: Fin n→Sec G d): P w= ∑ z: Fin n→ Fin (d+1), P (fun i=> en (show _≤d from Nat.lt_add_one_iff.mp (z i).isLt) (part d (z i) (w i))) := by
  have he:= P.map_sum (fun i (j: Fin (d+1))=> en (show j.val ≤ d from Nat.lt_add_one_iff.mp j.isLt) (part d j (w i))); simpa only [enfits] using he
lemma stepped (d j:ℕ): recruit (step d) (batch D g (d+1) j)=batch D g d j :=by
  ext n t q; rw [calls _ q,calls (batch D g d j n t) q]; apply Finset.sum_congr rfl; intro a _; rw [recruits,upper]; exact upper D g _ (fun i=> Nat.le_of_lt (a i).isLt) _ _

variable {X:Type*} {F:Filter X} {a:X→Mesh}

omit g in
theorem waist (H : Stretched F a) (p:Fin n→ Sec G d) (K:Set (Points n)) (hk:IsCompact K) (hx:K⊆conf n) :
    ∃ C:ℝ, 0≤ C ∧ ∀ᶠ i in F, ∀ t:Test n, tsupport t ⊆ K → ∀ b:ℝ, Bound t b →
      ‖batch D (a i) d 0 n t p-reference G d n t p‖≤ b*C*(a i).spacing := by
  let V (r:Fin n→Fin (d+1)) (t:Test n):= in_grade (reference G d n t) r (fun i=>part d (r i) (p i)); let U (r:Fin n→Fin (d+1)) (i:X) (t:Test n):= in_grade (batch D (a i) d 0 n t) r (fun i=>part d (r i) (p i))
  have Hc (r): ∃ C:ℝ, 0≤C ∧ ∀ᶠ i in F, ∀ t:Test n, tsupport t ⊆ K → ∀ b:ℝ, Bound t b → ‖U r i t -V r t‖≤ b*C*(a i).spacing:=by
    simp_rw [U,indicated]; exact Mesh.leading_order D (fun i=>(r i).val) (fun i=>part d (r i).val (p i)) H _ hk hx
  choose C h he using Hc; refine ⟨∑ r,C r, Finset.sum_nonneg (fun r _=> h r),?_⟩
  filter_upwards [eventually_all.mpr he] with i Hi t Ht b hb
  rw [calls _ p,calls (reference G d n t) p, ← Finset.sum_sub_distrib,Finset.mul_sum, Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun r _=> Hi r t Ht b hb))

omit g in
lemma cost_window (H:Stretched F a) (t:Test n) (p: Fin n→Sec G d): Rate F a (fun i=>batch D (a i) d 0 n t p) (fun _=>reference G d n t p):=by
  obtain ⟨b,_,hb⟩:= bound_fin t; obtain ⟨C,_,hc⟩:= waist D H p _ t.hasCompactSupport t.tsupport_subset
  exact Rate.introduce (b*C) (hc.mono fun _ h=> h t (Set.Subset.refl _) b hb)
end YM.XSpace.Normalize
