import YM.MS.Local.Monomial
/-!
# Spans of ordered tiles on the momentum list

Use first-slot `bud`. Later the A-only symmetric part and the BRST homotopy
on its precursor are used. No momentum delta, hence no exceptions at arity zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open scoped Topology ContDiff
variable {A P D : Type}

/-- Extensive unmarked unit separately. This value is a local scalar. -/
def hit (w : Legs (Mode A P)) : ℂ:= if w.length=0 then 1 else 0
@[simp] lemma hit_nil : hit (A:=A) (P:=P) []=1:=by simp [hit]
@[simp] lemma hit_cons i l : hit (A:=A) (P:=P) (i::l)=0:=by simp [hit]
-- finite arity string as rank-state tensor
def line : (n:ℕ)→ (Fin n→Twig A P) → Row A P ℂ
    | 0, _=> hit
    | n+1, p=> bud (p 0) (line n (p ∘ Fin.succ))
lemma line_zero (p:Fin 0→Twig A P) : line 0 p=hit:=rfl
lemma line_bud (n:ℕ) (p:Fin (n+1) → Twig A P): line (n+1) p=bud (p 0) (line n (p∘Fin.succ)):=rfl
lemma line_cons {n:ℕ} (f: Twig A P) (p:Fin n→Twig A P): line (n+1) (Fin.cons f p)=bud f (line n p):=by
   rw [line_bud,Fin.cons_zero]; rw [show Fin.cons f p ∘ Fin.succ = p from funext fun i=> Fin.cons_succ ..]

variable (w c : A→ℤ) [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma cub_hit : Cub w c 0 0 0 (hit (P:=P)) := by
   refine ⟨fun E _ _ u h=>?_, fun u hu=>?_,fun u hu=> if_neg hu⟩
   · cases u with
     | nil=> refine ⟨contDiff_const,fun h=>?_,fun u x=>?_⟩; norm_num [fieldDim] at h; simp only [show (0:ℤ)-fieldDim w ([]: List (Mode A (E →L[ℝ] P)))=0 from rfl,zpow_zero,one_smul,fieldVal,sail_nil]
     | cons i v => have he : fieldVal (hit (A:=A) (P:=P)) (i::v)=0 := funext fun x=> hit_cons _ _; rw [he]; exact form_zero _
   rcases u with _|i <;> first | exact False.elim (hu rfl) | exact hit_cons ..

lemma line_in {n:ℕ} {p:Fin n→Twig A P} {x y: Fin n→ℤ} (H : ∀ i, Star w c (x i) (y i) (p i)) : Cub w c (∑ i,x i) (∑ i,y i) n (line n p):= by
   induction n with
   | zero=> simpa only [line_zero,Fin.sum_univ_zero] using cub_hit (P:=P) w c
   | succ n ih=> rw [Fin.sum_univ_succ,Fin.sum_univ_succ, line_bud]; exact enters (H 0) (ih (fun i=> H (Fin.succ i)))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma line_rank {n:ℕ} (p:Fin n→Twig A P) {v:List (Mode A P)} (h:v.length≠n) : line n p v=0:= by
   induction n generalizing v with
   | zero=> exact if_neg h
   | succ n ih=> cases v with
     | nil=> rfl
     | cons i v=> exact mul_eq_zero_of_right _ (ih _ (by simpa using h))
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma line_gaze {n:ℕ} (p:Fin n→Twig A P) (a:Fin n→A) (q:Fin n→P): line n p (gaze a q)=∏ i,p i (a i,q i):= by
   induction n with
   | zero=> simp [line,gaze]
   | succ n ih=> rw [show gaze a q=(a 0,q 0)::gaze (a∘Fin.succ) (q∘Fin.succ) from by simp [gaze,List.ofFn_succ],line_bud,bud_cons, ih, Fin.prod_univ_succ]; rfl

variable (A P)
def Loom (h d : ℤ) (r:ℕ) : Submodule ℂ (Row A P ℂ) := Submodule.span ℂ {f: Row A P ℂ| ∃ (F : Fin r→ Twig A P) (x y:Fin r→ℤ), (∀ i, Star w c (x i) (y i) (F i))∧(∑ i,x i)=h ∧(∑ i,y i)=d ∧ line r F=f }
variable {A P} {q h ζ : ℤ} {r : ℕ} {f : Row A P ℂ}
lemma Tile_inside : Loom (A:=A) (w:=w) (c:=c) P h q r ≤ tile (w:=w) (c:=c) P h q r := Submodule.span_le.mpr (fun F hv => by obtain ⟨p,x,y,H,hx,hy,rfl⟩:= hv; rw [← hx, ← hy]; exact tileCub.mpr (line_in w c H)) -- args order explicit?
lemma line_loom {p:Fin r→Twig A P} {x y:Fin r→ℤ} (hx : ∀ i, Star w c (x i) (y i) (p i)) (hy : (∑ i, x i)=h) (hp : (∑ i, y i)=q) : line r p∈Loom (A:=A) (w:=w) (c:=c) P h q r:= subset_span (mem_setOf.mpr ⟨p,x,y,hx,hy,hp,rfl⟩)
end YM.MS.Local
