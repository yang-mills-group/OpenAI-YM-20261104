import YM.AlbaMS.Super.Drip

/-!
Paths under linear change; reversing density kernels to Lagrangians and
translations. Only old support fixed on push base. No measurability issues
here. Also works with both grading patterns on Cov & BV-Laplacian.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function
open scoped BigOperators Classical
variable {ι κ τ R : Type*} [CommRing R] {ρ : ι→Bool} {σ : κ→Bool} {ϕ : τ→ Bool}
variable {F G : Coil ρ R} (k : ι→ι→R)(g:κ→κ→R){s u : Finset ι}{t:Finset κ} {n j :ℕ} {x :κ} {l : List κ}
variable {A : ι→κ→R}{H:Routes ρ σ A}
lemma Cap.dripper (h:Cap F (n+1)): Cap (drip s A x F) n:= by rw [drip_apply]; exact Cap.sum _ _ fun i _=> (h.dz i).smul _
lemma Heg.dripper (h:Heg (n+1) F): Heg n (drip s A x F):= by rw [drip_apply]; exact Heg.sum _ _ fun i _=> (h.D_zone i).smul _
lemma Heg.shoot (h:Heg n F): Heg n (shot s A H F):=by
  intro l; induction l generalizing F n with
  | nil=> exact fun hv=>h _ hv
  | cons i l ih=>
    intro he; rw [← D_read,shot_D] at he; obtain _|n:=n
    · have ht:drip s A i F=0:=by rw [(h.cap _ _).eroded,drip_apply]; simp
      exact False.elim (he (by rw [ht,map_zero,zero_apply]))
    rw [List.length_cons,ih h.dripper he]
lemma Cap.shoots (h:Cap F n): Cap (shot s A H F) n:=by
  rw [← ranks F n h,map_sum]; exact Cap.sum _ _ fun i hi=> Cap.up ((rankn.heg F i).shoot.cap _ _) (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
lemma Tome_approve {p}(h:Tone p F): Tone p (shot s A H F):=by
  intro l; induction l generalizing F p with
  | nil=> exact fun hv=>h [] hv
  | cons x l ih=> intro hf; rw [← D_read,shot_D] at hf; rw [band_cons,ih (Tone.drips A H h) hf]; cases p<;>cases σ x<;>rfl
lemma shot_touch : touch g t (shot s A H F) = shot s A H
    (touch (fun i j=> ∑ a∈ t,∑ b∈ t,A i a*g a b * A j b) s F) := by
  unfold touch; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,shot_D,map_sum]
  -- want move shot outside. keep operations separated initially
  simp_rw [← map_smul (shot s A H), ← map_sum (shot s A H)]
  congr 1; simp_rw [drip_apply,map_sum,map_smul,Finset.smul_sum,Finset.sum_smul];
  -- reorder one stripe with three nested sectors
  let P i j x y:=(A i x*g x y*A j y) • (D j (D i F))
  simp_rw [smul_smul,show ∀ x y i j, g x y*(A i y*A j x)=A j x*g x y*A i y by intros; ring]
  change (∑ x∈t,∑ y∈t,∑ j∈s,∑ i∈s,P i j x y) = ∑ i ∈ s,∑ j ∈s,∑ x∈t,∑ y∈t,P i j x y
  simp_rw [Finset.sum_comm (s:=t) (t:=s)]; rw [Finset.sum_comm]

lemma shot_touched {g' : ι→ι→R}(hp:∀ i∈s,∀ j∈s, g' i j=∑ a∈t,∑ b∈ t,A i a*g a b * A j b):touch g t (shot s A H F) = shot s A H (touch g' s F):=by
  rw [shot_touch]; congr 1; rw [touch_apply,touch_apply]; refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=>?_ ; rw [hp i hi j hj]
lemma shot_cross (p:Bool) {g' : ι→ι→R}(hp:∀ i∈s,∀ j∈s, g' i j=∑ a∈t,∑ b∈ t,A i a*g a b * A j b): cross p g t (shot s A H F) (shot s A H G)= shot s A H (cross p g' s F G):=by unfold cross; simp_rw [← shot_mul A H, shot_touched g hp,← shot_plane A H]; simp [shot_mul] -- direction
variable {B : κ→ τ→ R}{N:ι→τ→ R}{J:Routes σ ϕ B} {M:Routes ρ ϕ N}
lemma accumulate (h:∀ i∈ s,∀ j,N i j=∑ a∈ t,A i a *B a j): shot t B J (shot s A H F)= shot s N M F:=by
  ext l; induction l generalizing F with | nil=> simp [shot_nil]|cons i l ih=>
    rw [← D_read, ← D_read (F:=shot s N M F),shot_D,shot_D]; simp only [drip_apply,map_sum,map_smul, shot_D,Finset.smul_sum]
    rw [Finset.sum_comm]; simp_rw [sum_read,smul_smul,smul_read,ih]; refine Finset.sum_congr rfl fun j hj=> ?_; rw [h j hj, Finset.sum_mul]; simp_rw [mul_comm (B _ i) (A j _)]

lemma shoots_id {A : ι→ι→R}{H:Routes ρ ρ A}(h:∀ i∈s,∀ j,A i j=ite (i=j) 1 0)(t:Inside (s:Set ι) F): shot s A H F=F:=by
  ext l; induction l generalizing F with | nil=>exact shot_nil ..| cons i l ih=>
    have he:drip s A i F=D i F:=by
      rw [drip_apply]; refine (Finset.sum_congr (s₂:=s) (g:=fun j=> (if j=i then (1:R) else 0) • D j F) rfl (fun j hj=> by rw [h j hj i])).trans ?_
      by_cases ht:i∈s <;> simp [ht,t.erased]
    rw [← D_read _ _ _,shot_D,he, ih (t.dz i)]; rfl

variable [Algebra ℚ R]
lemma shot_wither {g' : ι→ι→R}(hp:∀ i∈s,∀ j∈s, g' i j=∑ a∈t,∑ b∈ t,A i a*g a b * A j b)(tv: FinRank F): wither g t (shot s A H F)=shot s A H (wither g' s F):=by
  let n:=tv.choose; have he:n≤2*n:= by omega
  rw [withers tv.choose_spec.shoots he, withers tv.choose_spec he, twig_apply,twig_apply,map_sum]; refine Finset.sum_congr rfl fun i hi=> ?_
  simp_rw [pe_apply,map_smul]; congr 1; clear hi; induction i with|zero=>rfl|succ i ih=>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply, ih, shot_touched g hp]
end YM.MSBar.Bric.Coil
