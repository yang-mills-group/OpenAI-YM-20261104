import YM.FormalBulk08.Avenue.Junction
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Taft
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Avenue Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X I:Type}{W:Lab G K I}{ρ:ChartRatio G}{E e r d D R:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
section
variable {Z N: Pennants (Letter F)}{u v:Letter F→ℝ}
lemma nc_roll (h:Found (Pose.slots F) (Pose.weight F) Z u)(p:Found (Pose.slots F) (Pose.weight F) N v): noncontract F (Z*N)=noncontract F Z * noncontract F N:= by
   ext i j;rw [Matrix.mul_apply];unfold noncontract; split
   next h' =>
      rw [Roof.slope_sum]; apply Finset.sum_congr rfl; intro k hk; by_cases hv:Pose.slots F i=Pose.slots F k
      · rw [if_pos hv,if_pos (hv.symm.trans h')]
      rw [if_neg hv,zero_mul]; rcases (lt_or_gt_of_ne hv) with hx|hx; rw [p.bound _ _ (h' ▸ hx),mul_zero];rw [h.bound _ _ hx,zero_mul]
   next he=>
      symm; apply Finset.sum_eq_zero; intro k hk; by_cases hz: Pose.slots F i=Pose.slots F k
      · rw [if_neg (fun hh=>he (hz.trans hh)),mul_zero]
      rw [if_neg hz,zero_mul]
lemma nc_identity (F:Frame G d): noncontract F 1=1:= by ext i j; by_cases h:i=j <;> simp [noncontract,h,Matrix.one_apply]
lemma nc_revert (h:Colfax (slots F) (Pose.weight F) Z u): (noncontract F Z)⁻¹=noncontract F Z⁻¹:= by
   have he:= nc_roll (primes (down h)) (down h); rw [Matrix.nonsing_inv_mul _ h.det,nc_identity] at he;exact (left_inv_eq_right_inv he.symm (Matrix.mul_nonsing_inv _ (tagBack (nc_stamp Z u h)).1)).symm
lemma high_up (L:Side)(i j:Letter F)(h:Pose.weight F j<Pose.weight F i): 0≤ heightK L d (Pose.weight F i)* (heightK L d (Pose.weight F j))⁻¹ ∧ heightK L d (Pose.weight F i)*(heightK L d (Pose.weight F j))⁻¹ ≤ (L.val:ℝ)⁻¹:= by
    rw [heightK_of_le L (weightFits F i), heightK_of_le L (weightFits F j), ← inv_pow]; have he : d-Pose.weight F i+1≤d-Pose.weight F j:=by have :=weightFits F i;omega
    let l:ℝ:= (L.val:ℝ); let x:=d-Pose.weight F i; have hp:1 ≤ l:= Nat.one_le_cast.mpr L.property; have hx:0<l:=zero_lt_one.trans_le hp; refine ⟨by positivity, le_trans ?_ (le_of_eq (show l^x*(l⁻¹)^(x+1)=l⁻¹ by rw [pow_succ,←mul_assoc,←mul_pow,mul_inv_cancel₀ hx.ne',one_pow,one_mul])) ⟩
    apply mul_le_mul_of_nonneg_left (?_) (pow_nonneg hx.le _); exact pow_le_pow_of_le_one (inv_nonneg.mpr hx.le) (inv_le_one_of_one_le₀ hp) he
end
-- Basis conversion B^N. diagonal no contractions.
structure Mob (F: Frame G d) (A: Matrix (Letter F) (Letter F) ℝ) :Prop where
    unit : ∀ i,A i i=1
    raiseS:∀ i j,A i j≠0→ i≠j→ Pose.slots F i=Pose.slots F j ∧ Pose.weight F j < Pose.weight F i
lemma empty_mob (F:Frame G d) : Mob F 1 := by refine ⟨fun i=>Matrix.one_apply_eq i,fun i j h hp=>?_⟩; exact (h (Matrix.one_apply_ne hp)).elim

def revise (F:Frame G d)(L:Side) :Matrix (Letter F) (Letter F) ℝ:= Matrix.diagonal (fun i=> heightK L d (Pose.weight F i))
def wheel (F:Frame G d) (B:Matrix (Letter F) (Letter F) ℝ) (L:Side) (T:Pennants (Letter F)):= revise F L* B *(noncontract F T)⁻¹
lemma wheel_visit {B:Matrix (Letter F) (Letter F) ℝ}{T:Pennants (Letter F)}{L:Side}(h:Colfax (slots F) (Pose.weight F) T (fun i=> heightK L d (Pose.weight F i)))(i j): wheel F B L T i j=heightK L d (Pose.weight F i) * (B i j*(heightK L d (Pose.weight F j))⁻¹ + ∑ k ∈ Finset.univ.erase j,B i k*((noncontract F T)⁻¹ k j)) := by
    rw [wheel,mul_assoc, revise, Matrix.diagonal_mul, Matrix.mul_apply, nc_revert h]
    congr 1; rw [←Finset.add_sum_erase _ _ (Finset.mem_univ j)]; rw [show noncontract F T⁻¹ j j=_ from (show noncontract F T⁻¹ j j=(heightK L d (Pose.weight F j))⁻¹ from (by unfold noncontract; rw [if_pos rfl];exact (primes (down h)).due _))]
lemma nc_mob {Z:Pennants (Letter F)}{b:Letter F→ℝ}(hp:Colfax (slots F) (Pose.weight F) Z b) (i j)(h: (noncontract F Z)⁻¹ i j≠0)(e:i≠j): slots F i=slots F j∧Pose.weight F j<Pose.weight F i:= by
    rw [nc_revert hp] at h; unfold noncontract at h; split at h
    next he => have hv:=(primes (down hp)).min i j h e; omega
    exact (h rfl).elim
lemma overstep {B:Matrix (Letter F) (Letter F) ℝ}{T:Pennants (Letter F)}{L:Side}(h: Mob F B)(p:Colfax (slots F) (Pose.weight F) T (fun i=>heightK L d (Pose.weight F i))) : Mob F (wheel F B L T):= by
   let H:= noncontract F T
   have hX(i j k) (hp:k≠j) (hv:B i k*H⁻¹ k j≠0): Pose.slots F i=Pose.slots F j ∧ Pose.weight F j<Pose.weight F i:= by
       have hx:= nc_mob p k j (right_ne_zero_of_mul hv) hp
       by_cases hh:i=k
       · subst k; exact hx
       obtain ⟨a,b⟩:= h.raiseS i k (left_ne_zero_of_mul hv) hh; omega
   refine ⟨fun i=>?_,fun i j he hp=>?_⟩
   · rw [wheel_visit p,h.unit i,one_mul,Finset.sum_eq_zero,add_zero,mul_inv_cancel₀ (p.paid i).ne']
     intro k hk; by_contra hh; have hx:=hX i i k (Finset.ne_of_mem_erase hk) hh; omega
   rw [wheel_visit p] at he
   by_cases ht:B i j≠0; exact h.raiseS i j ht hp
   simp only [not_ne_iff.mp ht, zero_mul, zero_add] at he; obtain ⟨k,hk,hP⟩:= Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul he); exact hX i j k (Finset.ne_of_mem_erase hk) hP
end YM.FormalBulk08.Taft
