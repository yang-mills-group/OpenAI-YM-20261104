import YM.Contacts.Power.Rating

/-! Absolute (rather than one-sided) upper bounds with slack; these compose
through fixed finite depth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Power
open Function Filter
open scoped Topology BigOperators
variable {α X Y : Type*} {P:Pace α} {a b:ℝ} {f g:α→X} {u:α→Y}

namespace Pace.Priced
section
variable [SeminormedAddGroup X]

lemma mono (h:P.Priced a f) (he:a≤b) : P.Priced b f := fun c hc=> h c (he.trans_lt hc)
lemma cheaper (h:P.Priced a f) (hs : ∀ᶠ i in P.net,‖g i‖ ≤ ‖f i‖) : P.Priced a g :=
  fun b hb => (hs.and (h b hb)).mono fun i hi=> hi.1.trans hi.2
lemma congr (h:P.Priced a f)(he:f =ᶠ[P.net] g) : P.Priced a g:= h.cheaper (he.mono fun i h=> (congr_arg norm h).symm.le)
lemma exacts (h:∀ b:ℝ,a<b → P.Priced b f) : P.Priced a f:= by intro b hb; obtain ⟨c,hc,hx⟩:= exists_between hb; exact h c hc b hx

lemma of_product [SeminormedAddGroup Y] {Z:Type*}[Norm Z]{v:α→ Z} (h:P.Priced a f)(hh:P.Priced b u)
    (he : ∀ᶠ i in P.net,‖v i‖ ≤ ‖f i‖*‖u i‖): P.Priced (a+b) v:= by
  intro c hc
  have hb:b<c-a := by linarith
  obtain ⟨p,hp,hq⟩:=exists_between hb
  filter_upwards [h (c-p) (by linarith),hh p hp,he] with i hi hx hd
  exact hd.trans ((mul_le_mul hi hx (norm_nonneg _) (P.rate_pos .. |>.le)).trans_eq
    ((P.rate_add (c-p) p i).symm.trans (by rw [sub_add_cancel]))) -- norm_nonneg .. requires Norm nonneg (not raw)
end
section
variable [SeminormedAddGroup X]
lemma add_cap (h:P.Priced a f)(hx:P.Priced a g) : P.Priced a (fun i=> f i+g i) := by
  intro c hc
  obtain ⟨p,hp,hq⟩:= exists_between hc
  have hy:= (((P.rate_grade p).combine (P.rate_grade p)).upper hq)
  filter_upwards [h p hp,hx p hp,hy] with i hi ht hx using (norm_add_le ..).trans ((add_le_add hi ht).trans hx)
lemma add (h:P.Priced a f)(hx:P.Priced b g) : P.Priced (max a b) (fun i=> f i+g i) :=
  add_cap (h.mono (le_max_left ..)) (hx.mono (le_max_right ..))
lemma neg (h:P.Priced a f) : P.Priced a (fun i=>-f i) := h.cheaper (by simp)
lemma sub_cap (h:P.Priced a f)(hx:P.Priced a g) : P.Priced a (fun i=> f i-g i) := by
  simp_rw [sub_eq_add_neg]; exact h.add_cap hx.neg
lemma sub (h:P.Priced a f)(hx:P.Priced b g) : P.Priced (max a b) (fun i=> f i-g i) := by
  simp_rw [sub_eq_add_neg]; exact h.add hx.neg
lemma from_bound (C:ℝ) (h:∀ᶠ i in P.net, ‖f i‖ ≤ C) : P.Priced 0 f:= by
  intro b hb; exact (h.and ((P.rate_grow hb).eventually_ge_atTop C)).mono fun i hi=>hi.1.trans hi.2
lemma constants (x:X) : P.Priced 0 fun _=> x:= from_bound ‖x‖ (by simp)
lemma zeros (P : Pace α) (a : ℝ) : P.Priced a fun _=> (0:X) := by
  simp only [Priced,norm_zero]; exact fun b _=> Eventually.of_forall fun i=> P.rate_pos b i|>.le
end

lemma abs_cost [SeminormedAddGroup X](h:P.Priced a f): P.Priced a (fun i=> ‖f i‖):=by simpa only [Priced,Real.norm_of_nonneg (norm_nonneg _)] using h
lemma of_abs [SeminormedAddGroup X](h:P.Priced a (fun i=> ‖f i‖)) : P.Priced a f:=by simpa only [Priced,Real.norm_of_nonneg (norm_nonneg _)] using h
lemma sum [SeminormedAddCommGroup X] (A:Finset Y)(C:Y→α→X)(h:∀ i∈A,P.Priced a (C i)) : P.Priced a (fun i=>∑ j∈A,C j i):=by
  classical
  induction A using Finset.induction_on with
  | empty=>simpa using zeros (X:=X) P a
  | insert i t hi ih=> simp_rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self ..)).add_cap (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))

lemma mul [NonUnitalSeminormedRing X] (h:P.Priced a f)(he:P.Priced b g): P.Priced (a+b) (fun i=> f i*g i):=
  h.of_product he (Eventually.of_forall fun i=> norm_mul_le ..)
lemma powers [SeminormedRing X] (h:P.Priced a f)(n:ℕ): P.Priced (n*a) (fun i=> f i^n):=by
   induction n with
   | zero=>simpa using (constants (P:=P) (1:X))
   | succ n ih=>simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul,Nat.cast_succ] using ih.mul h
lemma smul [SeminormedAddCommGroup X] [NontriviallyNormedField Y] [NormedSpace Y X] (hu:P.Priced a u)(h:P.Priced b f): P.Priced (a+b) (fun i=> u i • f i):=hu.of_product h (Eventually.of_forall fun i=>norm_smul_le ..)
-- often use one-sided `Priced` on nonnegative exps
lemma upper {f:α→ℝ} (h:P.Priced a f){b:ℝ}(hb:a<b): ∀ᶠ i in P.net,f i≤ P.rate b i := (h _ hb).mono fun i hi=> (Real.le_norm_self _).trans hi
lemma pay {f g:α→ℝ}(h:P.Priced a f)(he:P.Rating b g)(hp:a<b): ∀ᶠ i in P.net, f i ≤ g i:= (he.alsos h hp).mono fun i hi=> (Real.le_norm_self _).trans hi
lemma sinks [SeminormedAddGroup X](h:P.Priced a f)(hq:a<0): Tendsto f P.net (𝓝 0):=by
  obtain ⟨v,hv,hV⟩:= exists_between hq
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) (h _ hv) (P.rate_sink hV)) -- check
end Pace.Priced

namespace Pace
variable {F:Filter α} [SeminormedAddGroup X]
def refine (P : Pace α)(h:F ≤ P.net) : Pace α:= ⟨F,P.scale,P.deep.mono_left h⟩
lemma Priced.retain (h:P.Priced a f)(hk:F ≤ P.net) : (P.refine hk).Priced a f:= fun b hb=> (h b hb).filter_mono hk
lemma Rating.retain {f:α→ℝ}(h:P.Rating a f)(hk:F ≤ P.net) : (P.refine hk).Rating a f:= ⟨h.pos.filter_mono hk,h.tends.mono_left hk⟩
lemma Longer.retain {f:α→ℝ}(h:P.Longer a f)(hk:F ≤ P.net) : (P.refine hk).Longer a f:= fun b hb=> (h b hb).filter_mono hk
end Pace
end YM.Contacts.Power
