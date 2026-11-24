import YM.RG11Scheme.Bell.Signal

/-! Radial-column recovery under signed pull, including negative-root shifts. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.RG11Scheme.Bell
open Function Filter Set Lattice Mesh Maxwell Stencil Stencil.Shot Stencil.Point Stencil.Cell Pert Full Labels Tensor Hinge
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}{p d:ℕ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "α" => Bond G

def push (f:Cover→ E)(s:Signed)(x:Cover) := f (s.act x)
omit [NormedSpace ℝ E] in
lemma signed_positive (s:Signed)(i:Axis)(h:s.flip i=false) : s.act (step i:Cover)=step (s.perm i) := by simpa only [posDir,Lattice.Step.rotate,Lattice.Step.vec,h,Bool.false_eq_true, ↓reduceIte, Bool.xor_false] using Eq.symm (Lattice.Step.vec_rotate (posDir i) (R:=ℤ) s)
omit [NormedSpace ℝ E] in
lemma signed_negative (s:Signed)(i:Axis)(h:s.flip i=true) : s.act (step i:Cover)= -step (s.perm i) := by simpa only [posDir,Lattice.Step.rotate,Lattice.Step.vec,h,Bool.false_eq_true, ↓reduceIte, Bool.false_xor] using Eq.symm (Lattice.Step.vec_rotate (posDir i) (R:=ℤ) s)
lemma turn_hill {f:Cover→ E} (hf:f∈hill E d)(s:Signed) : push f s∈hill E d := by
   induction d generalizing f with
   | zero => apply hill_const_iff.2; unfold push; simp only [Signed.act_zero]; exact fun x=>hill_const_iff.mp hf _
   | succ n IH =>
      apply hill_single; intro i
      let a:= s.perm i
      have he:=sliced hf a
      let g:= fun x:Cover=>go [a] f (x-step a)
      cases e:s.flip i
      · rw [show go [i] (push f s)= push (go [a] f) s from ?_]
        · exact IH he
        funext x; unfold push; simp only [onwards,starting,Signed.act_add,signed_positive s i e];rfl
      rw [show go [i] (push f s)= -push g s from ?_]; rotate_left
      · funext x; unfold g push; simp only [onwards,starting,Signed.act_add,signed_negative s i e, ← sub_eq_add_neg,sub_add_cancel,Pi.neg_apply];dsimp [a]; abel
      exact (hill E n).neg_mem (IH (f:=g) (by unfold g;simp_rw [sub_eq_add_neg _ (step a)]; exact rise_cut _ he))
def Polar (A:Bond G)(d:ℕ) := ∀ i,findout A i∈hill G.Color d
lemma down_wind (A:α)(s:Signed)(hs : Polar A d) : Polar (Pert.Bare.wideLink G s A) d := by
   intro i; cases e:s.flip i
   · rw [show findout (Pert.Bare.wideLink G s A) i=push (findout A (s.perm i)) s from funext (fun x=> by simp [Pert.Bare.wideLink,findout,posDir, Lattice.Step.rotate, Lattice.Step.used,e,push,affine])]; exact turn_hill (hs _) _
   have hv : findout (Pert.Bare.wideLink G s A) i=(fun x => -push (findout A (s.perm i)) s (x+ step i)) := by funext x; simp [Pert.Bare.wideLink,findout, affine,Lattice.Step.rotate,posDir, e,Lattice.Step.used,push,signed_negative s i e,sub_eq_add_neg]
   rw [hv]; exact (hill G.Color d).neg_mem (rise_cut (step i) (turn_hill (hs _) _))
lemma row_signed (s:Signed)(x:Cover) : Ortho.move s.ortho (row x) = row (s.act x) := by ext i; obtain ⟨j,rfl⟩:=s.perm.surjective i; rw [Signed.ortho_move];simp [Signed.act_at]
lemma left_invframe (s:Signed)(P:Taylor G d)(x:Cover)(i:Axis) : brighten (Taylor.turn s.ortho⁻¹ P) (x,i)=(Align.Atom.tally s i) • brighten P (s.act x,s.perm i) := by
   unfold brighten; rw [Taylor.turn_value,inv_inv,row_signed];
   change ∑ k:Axis,star (s.matrix k i) • _=_
   rw [Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _)]
   · unfold Align.Atom.tally;rw [star_trivial,s.matrix_at,if_pos rfl]
   intro b _ hb; rw [star_trivial,s.matrix_at,if_neg (Ne.symm hb),zero_smul]
lemma higher_deg (P:Taylor G d): Polar (brighten P) (d+1) := fun i=> traces_grade (P.val i)
lemma boundary_wind (P:Taylor G d)(s:Signed) : Polar ((Pert.Bare.wideLink G s (brighten P))-brighten (Taylor.turn s.ortho⁻¹ P)) d := by
   let B:= brighten P
   intro i; let a:=s.perm i
   cases e:s.flip i
   · rw [show findout _ i=(0:Cover→G.Color) from ?_]; exact (hill G.Color d).zero_mem
     funext x; unfold findout; rw [Pi.sub_apply,Pert.Bare.wideLink_apply,left_invframe]; simp [posDir, Lattice.Step.rotate, Lattice.Step.used, Align.Atom.tally,e]
   rw [show findout _ i= -go [i] (push (findout B a) s) from ?_]; exact (hill G.Color _).neg_mem (sliced (turn_hill ((higher_deg P) a) s) i)
   funext x; unfold findout; rw [Pi.sub_apply,Pert.Bare.wideLink_apply,left_invframe]; simp [B,a,push,posDir, Lattice.Step.rotate,Lattice.Step.used,e, Align.Atom.tally, signed_negative s i e,sub_eq_add_neg]; abel
lemma radar (P:Taylor G d)(h:ℝ) : Pert.Bare.wideLinear G d h 0 (brighten P)=h^(-(d+2:ℤ)) • P := by
   rw [sided]; have he s : outside h s d (Pert.Bare.wideCore G d (affine s⁻¹ 0 (0:Cover)) (Pert.Bare.wideLink G s (brighten P)))= h^(-(d+2:ℤ)) • P := by
      unfold outside; rw [LinearMap.comp_apply, LinearMap.smul_apply]
      have H:= gem_dark _ (boundary_wind P s) (affine s⁻¹ 0 0)
      rw [map_sub,sub_eq_zero] at H; rw [H, capital,map_smul,←Taylor.turn_mul,mul_inv_cancel,Taylor.oneTurn]
   simp_rw [he]; rw [Finset.sum_const, Finset.card_univ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
lemma blank_core (A:α)(h:Polar A d)(u:ℝ)(x:Cover) : Pert.Bare.wideLinear G d u x A=0:= by rw [sided]; simp_rw [show ∀ s v,Pert.Bare.wideCore G d v (Pert.Bare.wideLink G s A)=0 from fun s v=> gem_dark _ (down_wind A s h) v,map_zero,Finset.sum_const_zero,smul_zero]
end YM.RG11Scheme.Bell
