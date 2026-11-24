import YM.UVExt.MainCauchy
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Laurent Lattice RG Wilson Precision Exterior Bid Matrix Set
open scoped Classical Topology ContDiff BigOperators
set_option linter.unusedSimpArgs false
variable {G : Gauge} {n : Side} (v : fieldDir G n 1)


def shifted {q} (t : Site n) (V : fieldDir G n q) : fieldDir G n q := fun z=>(V (t+z.1,z.2))
lemma shifted_link (t : Site n) (p : Walk) (x : Site n) : linkSum (collect _ (shifted t v)) x p = linkSum (collect G v) (t+x) p := by
  induction p generalizing x with
  | nil => rfl
  | cons d p ih =>
     rw [linkSum,linkSum,ih,←add_assoc]; congr 1
     split_ifs <;> simp_all [collect,Step.used,shifted,add_sub_assoc]
lemma shift_d (t : Site n) : dColor G n 1 (shifted t v) = shifted t (dColor G n 1 v) := by
   funext e
   obtain ⟨p,k,rfl⟩ := (show ∃ p k, (p,plaquette k)=e from ⟨e.1,plaqEquiv.symm e.2,Prod.ext rfl (plaqEquiv.apply_symm_apply _)⟩)
   rw [← fundamental]; change linkSum _ _ _ = dColor G n 1 v (t+p,plaquette k); rw [←fundamental]; exact shifted_link ..
lemma shift_pull (x : Site n) (s : Signed) : shifted x (pulled v s) = pulled (shifted (s.act x) v) s := by
   funext t
   unfold shifted pulled affine
   simp only [s.act_add, add_zero]
   generalize hq:(posDir (axisEquiv.symm t.2)).rotate s=d
   obtain ⟨d,h|h⟩:=d <;> simp [Step.used,add_sub_assoc]
lemma pulled_minus (w : Dir G n) s : pulled (v-w) s=pulled v s-pulled w s := by
  funext x
  simp only [pulled,Pi.sub_apply]
  split_ifs with hd
  · change -(_-_)=-((_):G.Color) - -((_):G.Color)
    abel
  rfl
lemma d_minus (w v : Dir G n) : dColor G n 1 (v-w)=dColor G n 1 v-dColor G n 1 w := by
   ext x i; simp only [Pi.sub_apply,PiLp.sub_apply] -- ext
   change (d 1 _ *ᵥ (parts G 1 v i-parts G 1 w i)) x= ((d 1 _ *ᵥ (parts G 1 v i)) - (d 1 n *ᵥ parts G 1 w i)) x
   exact congr_fun (Matrix.mulVec_sub ..) _
lemma grad_pull (s:Signed) : gradD (pulled v s) ≤ 16*gradD v := by
  apply (pi_norm_le_iff_of_nonneg (by unfold gradD; positivity)).mpr fun j=>?_

  have ht {V : Dir G n} (j) : deltaV j V = dColor G n 1 (shifted (step j) V - V) := by
      funext u; symm; change dColor G n 1 _ u= _; rw [d_minus,shift_d,Pi.sub_apply,delta_entry]; unfold shifted; congr 2; exact Prod.ext (add_comm (step (S:=Per n) j) u.1) rfl
  have hs : s.act (step j) = if (posDir j).rotate s |>.neg then -(step (s.perm j):Site n) else step (s.perm j) := ((posDir j).vec_rotate s |>.symm)
  rw [ht,shift_pull,←pulled_minus]
  apply le_trans (paid_curl _ _).2 (mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤16))
  rw [hs]; split_ifs
  · rw [d_minus]; conv_rhs => unfold gradD
    calc
      _ ≤ ‖deltaV (s.perm j) v‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> ?_
      _ ≤ _ := norm_le_pi_norm (fun j=>deltaV j v) (s.perm j)
    rw [Pi.sub_apply,shift_d]
    rw [norm_sub_rev]; apply le_trans _ (norm_le_pi_norm (deltaV (s.perm j) v) (i.1-step (s.perm j),i.2))
    rw [ht,d_minus,shift_d,Pi.sub_apply]
    unfold shifted; simp [Prod.mk.injEq]; congr 1; abel_nf; exact le_rfl
  rw [←ht]
  exact norm_le_pi_norm (fun i=>deltaV i v) _

end YM.UVExt.Paths
