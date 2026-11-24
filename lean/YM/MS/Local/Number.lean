import YM.MS.Local.Finite
/-! # Ghost number selects parity in all comparisons; local derivation (ordered slot)
 calculus and $Q H$ pairing creation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open scoped Topology ContDiff
variable {A P D : Type} {p: Sector A}
-- odd parity function explicit
def parity (g:ℤ) : Bool := decide (g % 2 = 1)
@[simp] lemma par_zero : parity 0=false:=rfl
@[simp] lemma par_one : parity 1=true:=rfl
@[simp] lemma par_neg (x:ℤ) : parity (-x)=parity x:= by
   by_cases h: x%2=1 <;> (simp [parity,h])
lemma par_add (u v : ℤ): parity (u+v)= ((parity u) ^^ (parity v)):= by
  by_cases h:u%2=1 <;> by_cases t:v%2=1 <;> (simp [parity,h,t]; omega)
lemma par_sub (u v : ℤ): parity (u-v)= ((parity u) ^^ (parity v)):= by rw [sub_eq_add_neg,par_add,par_neg]

-- Extend a one-cell matrix to raw rows while multiplying with full Koszul sign.
namespace MatrixLet
variable {b : Bool} {X : Shift ℂ (field p (P:=P)) b}
def one (X : Shift ℂ (field p (P:=P)) b) : Twig A P →ₗ[ℂ] Twig A P := {
   toFun f i:= ∑ j ∈ X.source i, X.mat i j * f j
   map_add' f g:=by ext; simp [mul_add,Finset.sum_add_distrib]
   map_smul' c f:=by ext; simp [mul_left_comm c,Finset.mul_sum] }
lemma matrix (X : Shift ℂ (field p (P:=P)) b) (f : Twig A P) i : one X f i=∑ j∈X.source i,X.mat i j*f j:= rfl
lemma acts (f : Twig A P) (H : Row A P ℂ) i l: X.Q (bud f H) (i::l)= one X f i * H l +cross b (p i.1)*(f i* X.Q H l):= by
   have ht j : D j (bud f H)= f j • H:=rfl
   rw [D_eval i (X.Q (bud f H)), X.deriving']; simp [Shift.hook,LinearMap.sum_apply,Finset.sum_apply,ht,map_smul,field,matrix,Finset.sum_mul,mul_assoc]
lemma exact_at (f : Twig A P) (H : Row A P ℂ) (c : Bool) (hf: ∀ i, f i≠0 → p i.1 = c): X.Q (bud f H) = bud (one X f) H + (cross b c:ℂ) • bud f (X.Q H) := by
   ext l; cases l with
   | nil=> simp
   | cons i l=> by_cases he:f i=0; simp [acts,he]; rw [acts]; simp [hf i he]
lemma no (X : Shift ℂ (field p (P:=P)) b) : X.Q hit=0:= by
   ext l; cases l with
   | nil=> simp
   | cons i l=>
       have he (j:Mode A P): D j hit=0:= by ext; simp
       rw [D_eval i (X.Q hit),X.deriving']; simp [Shift.hook,LinearMap.sum_apply,he]

lemma by_basis (X : Shift ℂ (field p (P:=P)) b) (f : Twig A P) (i:Mode A P): one X f i= X.Q (bud f hit) [i]:=by simp [acts]
variable {Z: Charge p P ℂ}
lemma charge [Fintype A] (f: Twig A P) (i:A) (q:P): one Z.move f (i,q)=∑ j:A,Z.table i j q*f (j,q):= by
   rw [by_basis]; change Z.raise _ _=_; rw [Charge.act_at]; simp [Charge.raise]
end MatrixLet

variable [NormedAddCommGroup P] [NormedSpace ℝ P] (w c : A → ℤ)
    {h q:ℤ} {r : ℕ}
open MatrixLet
lemma seed_test {f : Twig A P} (H : f∈seed P w c h q) i (he : f i≠0): parity (c i.1)=parity q:= by congr 1; contrapose! he; exact (seedStar.mp H).real' i he
-- reusable progression through any shift satisfying the grade laws on one letters.
section
variable {k:ℤ} (Q : Shift ℂ (field (parity ∘ c) (P:=P)) (parity k))

lemma loom_bud {f : Twig A P} {H : Row A P ℂ} {a b d e:ℤ} (hf : f∈seed P w c a d) (h : H∈ Loom A P w c b e r) :
      bud f H∈ Loom A P w c (a+b) (d+e) (r+1) := by
   -- `Loom A P w c`? args order
   change place A P f H ∈ _
   suffices HP : Loom A P w c b e r ≤ Submodule.comap (place A P f) (Loom A P w c (a+b) (d+e) (r+1)) from HP h
   rw [Loom,span_le]; rintro _ ⟨p,x,y,H,rfl,rfl,rfl⟩
   rw [SetLike.mem_coe,Submodule.mem_comap,place_at,← line_cons]
   refine line_loom w c (p:=Fin.cons f p) (x:=Fin.cons a x) (y:=Fin.cons d y) ?_ ?_ ?_
   exact fun i=> Fin.cases (by simpa only [Fin.cons_zero] using (seedStar.mp hf)) (fun k=> by simpa using H k) i
   all_goals simp [Fin.sum_univ_succ]
lemma qLoom (H0 : ∀ (h q:ℤ) (x: Twig A P), x∈seed P w c h q→ one Q x∈seed P w c h (q+k)) : Loom A P w c h q r ≤ Submodule.comap Q.Q (Loom A P w c h (q+k) r):= by
   induction r generalizing h q with
   | zero=> rw [Loom,span_le]; rintro _ ⟨p,x,y,H,rfl,rfl,rfl⟩; rw [SetLike.mem_coe,Submodule.mem_comap,line_zero,no]; exact zero_mem _
   | succ n ih=>
      rw [Loom,span_le]; rintro _ ⟨p,x,y,H,rfl,rfl,rfl⟩; rw [SetLike.mem_coe,Submodule.mem_comap,line_bud, Fin.sum_univ_succ,Fin.sum_univ_succ,MatrixLet.exact_at (c:= parity (y 0)) _ _ (seed_test w c (seedStar.mpr (H 0)))] -- wrong exact_at
      let b:=line n (p∘Fin.succ)
      have he := line_loom w c (fun i:Fin n => H i.succ) rfl rfl; have hu:= ih he
      refine add_mem ?_ (smul_mem _ _ ?_)
      · convert loom_bud w c (H0 _ _ (p 0) (seedStar.mpr (H 0))) he using 2; omega; rfl
      convert loom_bud w c (seedStar.mpr (H 0)) hu using 2; omega; rfl
end
end YM.MS.Local
