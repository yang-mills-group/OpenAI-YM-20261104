import YM.QuadraticLocal.Lamps
import YM.Corona.Fit

/-! Refile mixed terms of a signed physical regular family. All derivative
budgets, clear scalar roots and real masks remain on their original supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPrecontactSeparatedLamps
open Set Function Finset Lattice Wilson RG Marker QuadraticLocal Ac Push.AbsoluteSums
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {p:BudgetPoint} {V T ι : Type} [DecidableEq V]
    {R:Census V} {o:V→Site n} (L:Lamps T ι G p o R)

def portion (rows:Set ι) : Lamps T rows G p o R where
  mode i := L.mode i.val
  live i := L.live i.val
  address i := L.address i.val
  roots i := L.roots i.val
  nominal t i := L.nominal t i.val
  legal t i := L.legal t i.val
  clear i := L.clear i.val
  pure t i := L.pure t i.val

theorem split (rows:Set ι) [Fintype V] (t:T) (U:Config G n)
    (h:Summable (fun i=>L.frame i t U)) :
    (portion L rows).log t U + (portion L rowsᶜ).log t U = L.log t U :=
  h.tsum_subtype_add_tsum_subtype_compl rows

theorem reconciled {J:Type} (rows:Set ι) (old:Lamps T J G p o R) [Fintype V]
    (t:T) (U:Config G n) (h:Summable (fun i=>L.frame i t U)) (ho:Summable (fun i=>old.frame i t U)) :
    (L.join old).log t U = ((portion L rowsᶜ).join ((portion L rows).join old)).log t U := by
  have hp:=h.subtype rows
  have hs:=h.subtype rowsᶜ
  have sumP:Summable (fun i=> ((portion L rows).join old).frame i t U) :=
    (hp.hasSum.sum (f:=fun i=>((portion L rows).join old).frame i t U) ho.hasSum).summable
  rw [Lamps.joinLog (L:=L) (A:=old) t U h ho,
      Lamps.joinLog (L:=portion L rowsᶜ) (A:=(portion L rows).join old) t U hs sumP,
      Lamps.joinLog (L:=portion L rows) (A:=old) t U hp ho,
      ← split L rows t U h]
  ac_rfl

theorem subbill {f:ι→ℝ} {C:ℝ} (h:SumBudget f C) (s:Set ι) :
    SumBudget (fun i:s=>f i.val) C :=
  ⟨fun i=> h.1 i.val, h.2.1.subtype s,(h.2.1.tsum_subtype_le f s h.1).trans h.2.2⟩

theorem charged (rows:Set ι) {w:V→ℝ} {B:ℕ} {a C:ℝ} (h:L.Paid w B a C) :
    (portion L rows).Paid w B a C := by
  obtain ⟨f,nn,smooth,bill⟩:=h.budget
  exact ⟨fun i=>f i.val,fun i=>nn i.val,fun i=>smooth i.val,fun x=>subbill (bill x) rows⟩

theorem lower {w:V→ℝ} {B:ℕ} {a a' C:ℝ} (ha:a≤a') (hw:∀ v,0<w v)
    (h:L.Paid w B a' C) : L.Paid w B a C := by
  obtain ⟨f,nn,smooth,bill⟩:=h.budget
  refine ⟨f,nn,smooth,fun x=>budget_mono (bill x) ?_ ?_⟩
  · intro i
    split <;> first | exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (nn _)) (Real.exp_nonneg _) | rfl
  intro i
  split
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (mul_nonneg (Poly.worth hw _).le (nn _))
  exact le_rfl

theorem long (rows:Set ι) {w:V→ℝ} {B M:ℕ} {a C δ:ℝ} (hd:0≤δ) (hw:∀ v,0<w v)
    (span:∀ i:rows,M≤coverNumber B (L.ground i.val)) (h:L.Paid w B (a+δ) C) :
    (portion L rows).Paid w B a (Real.exp (-δ*M)*C) := by
  obtain ⟨f,nn,smooth,bill⟩:=h.budget
  refine ⟨fun i=> f i.val,fun i=>nn i.val,fun i=>smooth i.val,fun x=>?_⟩
  apply budget_mono (budget_scale (Real.exp_nonneg _) (subbill (bill x) rows))
  · intro i
    change 0 ≤ if x∈L.ground i.val then Poly.toll w (L.mode i.val)*f i.val*Real.exp _ else 0
    split <;> first | exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (nn _)) (Real.exp_nonneg _) | rfl
  intro i
  change (if x∈L.ground i.val then Poly.toll w (L.mode i.val)*f i.val*Real.exp (a*_) else 0)
    ≤ Real.exp (-δ*M)*(if x∈L.ground i.val then Poly.toll w (L.mode i.val)*f i.val*Real.exp ((a+δ)*_) else 0)
  by_cases hx:x∈L.ground i.val
  · simp only [if_pos hx]
    rw [mul_left_comm (Real.exp _),←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Poly.worth hw _).le (nn _))
    apply Real.exp_le_exp.mpr
    have hm: (M:ℝ) ≤ coverNumber B (L.ground i.val) := by exact_mod_cast span i
    change a*(coverNumber B (L.ground i.val):ℝ) ≤ -δ*M+(a+δ)*(coverNumber B (L.ground i.val):ℝ)
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hm)]
  simp [hx]

/-- Select all and only the entries involving at least two distinct original labels. -/
def mixed : Set ι := {i|1 < (L.mode i).val.card}

theorem separated {w:V→ℝ} {B M:ℕ} {a C δ:ℝ} (hd:0≤δ) (hw:∀ v,0<w v)
    (apart:∀ i∈mixed L, ∃ v∈(L.mode i).val, ∃ u∈(L.mode i).val,
      M*(4*B+2)+2*B ≤ separation (o v) (o u)) (h:L.Paid w B (a+δ) C) :
    (portion L (mixed L)).Paid w B a (Real.exp (-δ*M)*C) := by
  apply long L (mixed L) hd hw _ h
  intro i
  obtain ⟨v,hv,u,hu,d⟩:=apart i.val i.property
  have hD := d.trans (Corona.extent (L.ground i.val) B (L.roots i.val v hv) (L.roots i.val u hu))
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right hD) (by omega)

theorem at_sites {w:V→ℝ} {B:ℕ} {a C δ:ℝ} (hB:5≤B) (hd:0≤δ) (hw:∀ v,0<w v)
    (apart:∀ v u:V,v≠u → B^2+1 ≤ separation (o v) (o u)) (h:L.Paid w B (a+δ) C) :
    (portion L (mixed L)).Paid w B a (Real.exp (-δ*(B/8:ℕ))*C) := by
  apply separated L hd hw _ h
  intro i hi
  obtain ⟨v,hv,u,hu,hvu⟩:=Finset.one_lt_card.mp (show 1<(L.mode i).val.card from hi)
  refine ⟨v,hv,u,hu,?_⟩
  apply le_trans _ (apart v u hvu)
  have e:=Nat.div_mul_le_self B 8
  have t:=Nat.mul_le_mul_right B e
  have f:=Nat.mul_le_mul_right B hB
  have hh:4*(B/8)≤B:=by omega
  nlinarith only [t,f,hh]

end YM.Integration.WilsonPrecontactSeparatedLamps
end
