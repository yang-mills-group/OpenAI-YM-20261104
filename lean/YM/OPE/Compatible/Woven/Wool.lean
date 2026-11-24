import YM.OPE.Compatible.Parcels.Parcel
import YM.Planned.PRIMARY_INTEGRAL_295.Savings
/-! Array indexing. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Tree Next.Free Bloch Exterior
open scoped Topology BigOperators Classical
variable {r n:ℕ} {L:Side}
abbrev Keys (r:ℕ):= Fin r × Axis
abbrev Bin (r:ℕ):= Keys r→ℤ
def lace (r:ℕ): (Fin r→Cover) ≃ Bin r:= (Equiv.curry ..).symm
abbrev stepOut (x:Bin r) (i: Fin r):Cover:= lace r|>.symm x i
def couple (r:ℕ): Bin (r+1) ≃ Cover × Bin r where
    toFun x:= (stepOut x 0,lace _ fun i=> stepOut x i.succ)
    invFun y:= lace _ (Fin.cons y.1 (lace _|>.symm y.2))
    left_inv x:= by
        change lace _ _=_; apply (lace _|>.apply_eq_iff_eq_symm_apply).2; rw [(lace _).symm_apply_apply]; ext1 i; refine Fin.cases ?_ ?_ i
        · simp
        intro i; simp
    right_inv y:= by
        ext1; change stepOut (lace _ _) _= _; unfold stepOut; simp
        change lace _ _=_; apply (lace _|>.apply_eq_iff_eq_symm_apply).2; ext1 i; unfold stepOut; rw [(lace _).symm_apply_apply]; simp
lemma couple_start (x:Bin (r+1)) : (couple r x).1=stepOut x 0:=rfl
lemma couple_side (x:Bin (r+1)) (i:Fin r): stepOut ((couple r x).2) i=stepOut x i.succ :=rfl
lemma couple_size (x:Bin r) : size x=∑ i:Fin r,size (stepOut x i):=by unfold size; rw [Fintype.sum_prod_type]; rfl
lemma couple_total (x:Bin (r+1)) : size x=size ((couple r x).1)+size ((couple r x).2):=by rw [couple_size x,Fin.sum_univ_succ,couple_size ((couple r x).2)];rfl
lemma couple_shrunk (x:Bin (r+1)) (m:ℕ): poise m x ≤ poise m ((couple r x).1)*poise m ((couple r x).2):=by
    unfold poise; rw [← mul_pow, ← Nat.cast_mul]; gcongr; unfold notch; rw [couple_total]; nlinarith only
lemma couple_powers (x:Bin r) (m:ℕ): poise m x ≤ ∏ i, poise m (stepOut x i):=by
    induction r with
    | zero=> rw [poise,Fintype.prod_empty]; rw [notch,couple_size]; simp
    | succ n ih=> rw [Fin.prod_univ_succ]; apply (couple_shrunk x m).trans; exact mul_le_mul_of_nonneg_left (ih _) (zero_le_one.trans (poise_one m (stepOut x 0)))
abbrev weave (u:Fin r→Cover→ℝ)(x: Bin r) := ∏ i,u i (stepOut x i)
lemma trellis {f u:Fin r→Cover→ℝ} {A:Fin r→ℝ} (h:∀ i,Sack (u i) (f i) (A i)) (hg:∀ i,1 ≤ u i):
    Sack (weave u) (weave f) (∏ i,A i):=by
      induction r with
      | zero=>
        letI : Unique (Fin 0×Axis → ℤ):= inferInstance
        have h: Fintype (Bin 0):= Fintype.ofFinite (Bin 0)
        simp [Sack,SumBudget,weave]; exact (hasSum_fintype _).summable
      | succ r ih=>
        let Q:= weave f; let R:= weave u
        let E:= couple r
        let g (i:Fin r):= f i.succ; let w (i:Fin r):=u i.succ; let V:=weave g; let Z:= weave w; let a:= fun i:Fin r=> A i.succ
        have hh(p : Bin (r+1)): R p* ‖Q p‖ = (u 0 (E p).1*‖f 0 (E p).1‖)*(Z (E p).2 * ‖V (E p).2‖):=by unfold R Q weave; rw [Fin.prod_univ_succ, Fin.prod_univ_succ (f:=fun i=>f i (stepOut p i)),norm_mul]; change (u 0 (E p).1 * Z (E p).2) * (‖f 0 (E p).1‖ * ‖V (E p).2‖) = _; rw [mul_mul_mul_comm]
        have hv(i) : 0 ≤ R i:= prod_nonneg fun j _=> zero_le_one.trans (hg j _)
        have hs:= ih (f:=g) (u:=w) (A:=a) (fun j=> h j.succ) (fun j=>hg j.succ)
        have ht : Sack (R∘ E.symm) (Q∘ E.symm) (A 0*(∏ i:Fin r,a i)):= Sack.multiplex (h 0) hs (fun x=> le_of_eq (by simpa only [comp_apply,E.apply_symm_apply] using! hh (E.symm x))) (fun i=> hv _)
        rw [Fin.prod_univ_succ]; exact (show Sack R Q (A 0 * ∏ i:Fin r,a i) from by simpa [comp_def] using ht.adroit E)
end YM.OPE.Flume
