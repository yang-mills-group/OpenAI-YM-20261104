import YM.SchemeConversionRG11.FirstW.Invoice.Building
/-! Tadpole rules at the FIRST ORDER discrete stencil vertices. Not imposing rejection of ancestor contacts/free-pairs in general. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {X : Type*} [One X] [AddCommGroup X]
abbrev Pr (G : Gauge) (n : Side) := Edge (Site n) × G.ColorIndex
def snow (v : Pr G n) := needle v.1 (unitColor G v.2)
def bead (v : Pr G n) := pinch v.1 (unitColor G v.2)
lemma beads (p : FullT G n) : p=∑ v : Pr G n, bead v p • snow v := by
  rw [Fintype.sum_prod_type]; funext i
  simp only [Finset.sum_apply,bead,pinch_eq,snow,Pi.smul_apply, pinched]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; simp only [if_true]; exact inkSum _
  intro j _ hj; simp [Ne.symm hj]
def oneColor {G : Gauge} (v : G.Color) (x : Wind G X) : Prop := ∀ i,∃ r : ℝ,x i=r • v
lemma pool_eq0 (u v : Pr G n) (he : u.2 ≠ v.2) : pool (bead u) (bead v)=0 := by
  unfold pool bead; rw [branch_at,pinch_eq]; dsimp only [reflectT, Pi.add_apply,LinearMap.pi_apply,LinearMap.neg_apply,LinearMap.proj_apply, Orb.ghostLink]; rw [inner_add_right]; split_ifs <;> simp [inner_neg_right,real_inner_smul_right, unit_hit,he]
lemma atom_c (v : Pr G n) : oneColor (unitColor G v.2) (snow v) := by
  intro i; by_cases h:i=v.1; · exact ⟨1,by simp [h,snow,pinched]⟩
  exact ⟨0,by simp [snow,pinched,h]⟩
lemma boardAt_color (i : Step) (x : Four X) (A : Wind G X) (v : G.Color) (hA : oneColor v A) : ∃ r : ℝ, boardAt x i A = r • v := by
  obtain ⟨t,ht⟩:=hA (i.used x); simp only [boardAt,LinearMap.smul_apply,LinearMap.proj_apply,ht,smul_smul]; exact ⟨_,rfl⟩
lemma rail_color (x : Four X) (w : Walk) (A : Wind G X) (v : G.Color) (hA : oneColor v A) : ∃ r : ℝ, rail x w A = r • v := by
  induction w generalizing x with
  | nil=> exact ⟨0,by simp [rail]⟩
  | cons i w ih=>
    obtain ⟨b,hb⟩:=ih (x+i.vec); obtain ⟨c,hc⟩:=boardAt_color i x A v hA; rw [rail,LinearMap.add_apply,hb,hc]; exact ⟨c+b,(add_smul ..).symm⟩
lemma gear_color (s : Signed) (A : Wind G X) (v : G.Color) (hA : oneColor v A) : oneColor v (Bare.wideLink G s A) := fun i => by
  rw [Bare.wideLink_apply]; obtain ⟨c,hc⟩:=hA _ -- underscore
  rw [hc,smul_smul]; exact ⟨_,rfl⟩
lemma angle_bare (x : Four X) (w : Walk) (A B : Wind G X) (v : G.Color) (hA : oneColor v A) (hB : oneColor v B) : swerve x w A B=0 := by
  induction w generalizing x with
  | nil=>simp [swerve]
  | cons i w ih=>
    rw [swerve_eq,ih,add_zero]; obtain ⟨s,hs⟩:=boardAt_color i x A v hA; obtain ⟨b,hb⟩:=rail_color (x+i.vec) w B v hB; rw [hs,hb,G.ad.map_smul,LinearMap.smul_apply,G.ad v|>.map_smul,ad_diag0,smul_zero, smul_zero]
lemma orth_ad (u v : G.Color) : inner ℝ u (G.ad v u) = 0 := by linarith [podium v u u]
lemma angle_roll (x : Four X) (w : Walk) (A B : Wind G X) (v : G.Color) (hA : oneColor v A) : inner ℝ v (swerve x w A B)=0 ∧ inner ℝ v (swerve x w B A)=0 := by
  induction w generalizing x with
  | nil=>simp [swerve]
  | cons i w ih=>
    obtain ⟨s,hs⟩:=boardAt_color i x A v hA; obtain ⟨b,hb⟩:=rail_color (x+i.vec) w A v hA; obtain ⟨u,l⟩:=ih (x+i.vec)
    simp only [swerve_eq,inner_add_right,u,l,hs,hb,map_smul,LinearMap.smul_apply, real_inner_smul_right,orth_ad]; rw [ad_for v _, inner_neg_right,orth_ad]; simp
lemma tower_clean (x : Four X) (w : Walk) (A B C : Wind G X) (v : G.Color) (hA : oneColor v A) (hB : oneColor v B) : tower G x w A B C=0 := by
  obtain ⟨s,hs⟩:=rail_color x w A v hA; obtain ⟨b,hb⟩:=rail_color x w B v hB
  obtain ⟨hu,hv⟩:=angle_roll x w A C v hA; obtain ⟨hy,hz⟩:=angle_roll x w B C v hB
  simp only [tower_eq, spire,hs,hb,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.flip_apply,angle_bare x w A B v hA hB,angle_bare x w B A v hB hA,real_inner_smul_left, real_inner_smul_right,inner_add_right,hu,hv,hy,hz];simp
lemma sheer_clean (A B : Wind G X) (v : G.Color) (hA : oneColor v A) (hB : oneColor v B) (k : ℕ) (x : Four X) : sheer G k x A B = 0 := by
  have hp (A B : Wind G X) (hA : oneColor v A) (hB:oneColor v B) x : rush G x k A B=0 := by funext i a p; simp [rush,angle_bare (v:=v) (hA:=hA) (hB:=hB)]
  rw [sheer_eq,Finset.sum_eq_zero, smul_zero]; intro s _; rw [hp _ _ (gear_color _ A v hA) (gear_color _ B v hB),map_zero,map_zero]
lemma echo_clear (A B : Wind G X) (v : G.Color) (hA : oneColor v A) (hB : oneColor v B) (x : Four X) (k : Labels.Key G)(h : ℝ) : echoLeg h x k A B=0 := by
  simp only [echoLeg,LinearMap.smul_apply,echoAt,LinearMap.compr₂_apply,glint_once, sheer_clean A B v hA hB, sheer_clean B A v hB hA,add_zero,smul_zero,map_zero]
end YM.RG11.FirstW.Deck
