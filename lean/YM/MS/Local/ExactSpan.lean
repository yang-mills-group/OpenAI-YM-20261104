import YM.MS.Local.String
/-!
# No restrictions from evaluating the marked tensor only on arbitrary plane-wave charts

Finite polynomial reconstructs from those Taylor components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open scoped Topology ContDiff
variable {A P D : Type}
variable {w c : A→ℤ} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {v h q : ℤ} {r i j : ℕ}

section expand
-- Cut component rows by list of external species.
def sides [DecidableEq A] (p : Fin r→A) (f : Row A P ℂ): Row A P ℂ:= fun l=> if l.map Prod.fst= List.ofFn p then f l else 0
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma sides_rank [DecidableEq A] (p : Fin r→A) (f : Row A P ℂ) (l : Legs (Mode A P)) (h:l.length≠r): sides p f l=0:= if_neg (fun hx=> h (by simpa using congr_arg List.length hx))
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] lemma sides_eval [DecidableEq A] (p : Fin r→A) (f : Row A P ℂ) (g q) : sides p f (gaze g q)= if g=p then f (gaze g q) else 0:= by simp [sides,gaze,Function.comp_def]
lemma rebuild [Fintype A] [DecidableEq A] {f : Row A P ℂ} (H:Cub w c h q r f) : f=∑ p: Fin r→A, sides p f:= by
    ext l; rw [Finset.sum_apply]; by_cases hv:l.length=r
    · obtain ⟨g,p,rfl⟩:= discovered l hv; simp
    rw [H.rank l hv]; simp_rw [sides_rank (f:=f) _ _ hv,sum_const_zero]

variable (w c h q r) [Fintype D] [DecidableEq D] [DecidableEq A]
def logo (g : Fin r→A) (l : Fin i→ Fin r×D) (t:Fin r) : Twig A (Momentum D) := fun a=> if a.1=g t then oneLot l t a.2 else 0
omit [DecidableEq D] in
lemma logo_star (g:Fin r→A) (l:Fin i→Fin r×D) (t:Fin r): Star w c (w (g t)+(lot l t).card) (c (g t)) (logo r g l t):= by
    refine ⟨fun a=>?_,fun a he=>if_neg (fun (hk : a.1=g t)=>he (congr_arg c hk))⟩
    by_cases he:a=g t; subst a; simpa [logo] using lot_form l t
    simp only [logo,he,↓reduceIte]; exact form_zero _
omit [Fintype D] [DecidableEq D] in
lemma logo_line (g : Fin r→A) (l : Fin i→Fin r×D) (p u) : line r (logo r g l) (gaze u p) = if u=g then (poly l p:ℂ) else 0:= by
    rw [line_gaze]; split_ifs with h
    · subst u; simp [logo,lots]
    obtain ⟨k,hk⟩:= Function.ne_iff.mp h; exact Finset.prod_eq_zero (mem_univ k) (if_neg hk)
lemma side_member (g : Fin r→A) (f : Row A (Momentum D) ℂ) (H : Cub w c h q r f) : sides g f∈Loom A (w:=w) (c:=c) (Momentum D) h q r := by
    rcases lt_or_ge h (∑ i,w (g i)) with hu|hu
    · suffices L : sides g f=0 by rw [L]; exact zero_mem _
      ext l; unfold sides; split_ifs with h'
      · exact H.shape.no_tall l (fun he=> Bool.noConfusion he) (by unfold fieldDim; simp only [← List.map_map,h',List.map_ofFn]; simpa [Fin.sum_ofFn] using hu)
      rfl
    by_cases hv : (∑ i,c (g i))=q; swap
    · suffices L : sides g f=0 by rw [L]; exact zero_mem _
      ext l; unfold sides; split_ifs with h'
      · exact H.tag l (by unfold fieldDim; simp only [← List.map_map,h',List.map_ofFn]; simpa [Fin.sum_ofFn] using hv)
      rfl
    generalize hy : h-∑ i,w (g i) =k
    -- no in goal hv lost? hy
    lift k to ℕ using (show 0 ≤ k by omega)
    let T:= fun p=>f (gaze g p); have ht : Plane.Shape T k:= by rw [← hy]; exact H.visible g
    let K := Tensor.coeff T k 0
    let Y (l : Fin k→Fin r×D) := K (eye ∘ l)
    have hs : sides g f = ∑ l : Fin k→ Fin r×D, Y l • line r (logo r g l):= by
       ext l; rw [Finset.sum_apply]; by_cases he:l.length=r
       · obtain ⟨u,p,rfl⟩:= discovered _ he; simp_rw [sides_eval,Pi.smul_apply,logo_line]; split_ifs with h
         · subst u; exact (congr_fun ht.form p).trans (by simpa only [Y,smul_eq_mul,mul_comm _ (poly _ _:ℂ)] using tensor_spread K p)
         simp
       simp only [sides_rank (f:=f) _ _ he,Pi.smul_apply,line_rank _ he,smul_zero,sum_const_zero]
    rw [hs]; refine sum_mem (fun i _=> smul_mem _ _ (line_loom w c (logo_star w c r g i) ?_ hv)) -- `sum_mem` syntax
    rw [Finset.sum_add_distrib,← Nat.cast_sum,lot_size]; omega

theorem tile_eq [Fintype A] : tile (Momentum D) w c h q r=Loom A (w:=w) (c:=c) (Momentum D) h q r:= by
   refine le_antisymm ?_ (Tile_inside w c); intro f hv; have h' := tileCub.mp hv; rw [rebuild h']; exact sum_mem fun i _=> side_member w c h q r i f h'
end expand
end YM.MS.Local
