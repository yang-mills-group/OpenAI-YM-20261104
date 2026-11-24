import YM.Integration.ActualWilsonDirtyPartners
import YM.Integration.QLocalForcedTestForest

/-! The physical compulsory invoice can price the complete marked
spectators of each signed joined row. A nonempty touching set spends one
of the original per-site coupons, also when an arbitrarily distant
previously marked row belongs to that set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedTouchingPrice
open Function Finset Lattice RG Wilson Marker Overlay Push.AbsoluteSums MergeProof.Accent
open ActualWilsonTouchingVacuum ActualWilsonDirtyPartners
open scoped Classical BigOperators
variable {ι A V:Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] {Γ:Census V} {n:Side}

theorem touching_at (p:BudgetPoint) (D:ι→Support n) {b:ι→ℝ} {u margin:ℝ} (hmargin:0< margin) (hb:∀i,0≤ b i)
    (hit:∀y:Site n,SumBudget (fun i=>if y∈D i then p.mass (D i) (b i) else 0) u)
    (small:u*blockSites p.B≤ margin/2) (Y:Support n) :
    SumBudget (dirty p D Y b) ((2/margin)*(u*blockSites p.B)*Real.exp ((p.supportExponent+margin)*coverNumber p.B Y)) := by
  let k:ℝ:=coverNumber p.B Y
  let t:=u*blockSites p.B
  let x:ℝ:=Y.card*u
  have h0:0≤ u:=budget_nonneg (hit 0)
  have ht:0≤ t:=mul_nonneg h0 (by unfold blockSites; positivity)
  have hk:0≤ k:=Nat.cast_nonneg _
  have hx:0≤ x:=mul_nonneg (Nat.cast_nonneg _) h0
  have card:(Y.card:ℝ)≤ k*blockSites p.B:=by dsimp [k,blockSites]; exact_mod_cast Corona.pays Y p.B
  have vol:x≤ t*k:=by
    calc _≤(k*blockSites p.B)*u:=mul_le_mul_of_nonneg_right card h0
         _=_:=by dsimp [t]; ring
  have half:x≤ margin*k/2:=vol.trans (by have hh:=mul_le_mul_of_nonneg_right small hk; dsimp only [t]; linarith)
  have ex:Real.exp x-1≤(2/margin)*t*Real.exp (margin*k):=by
    have cap:k≤(2/margin)*Real.exp (margin*k/2):=by
      rw [div_mul_eq_mul_div,le_div_iff₀ hmargin]
      nlinarith only [Real.add_one_le_exp (margin*k/2)]
    calc _≤ x*Real.exp x:=increment x
         _≤(t*k)*Real.exp (margin*k/2):=mul_le_mul vol (Real.exp_monotone half) (Real.exp_pos _).le (mul_nonneg ht hk)
         _=t*(k*Real.exp (margin*k/2)):=by ring
         _≤ t*(((2/margin)*Real.exp (margin*k/2))*Real.exp (margin*k/2)):=mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right cap (Real.exp_pos _).le) ht
         _=_:=by rw [mul_assoc (2/margin),←Real.exp_add,show margin*k/2+margin*k/2=margin*k by ring]; ring
  have all:=products p D Y hb hit
  have old:=omit_one all (∅:Finset ι)
  have emp:invoice p D Y b ∅=Real.exp (p.supportExponent*k):=by simp [invoice,BudgetPoint.mass,k]
  rw [emp] at old
  have bare:SumBudget (dirty p D Y b) (Real.exp (p.supportExponent*k+x)-Real.exp (p.supportExponent*k)):=by
    apply budget_mono old
    · intro I
      by_cases hi:I=∅
      · simp [dirty,hi]
      · rw [dirty,if_pos hi]; exact all.1 I
    · intro I
      by_cases hi:I=∅ <;> simp [dirty,hi]
  apply budget_loosen bare
  change Real.exp (p.supportExponent*k+x)-Real.exp (p.supportExponent*k)≤(2/margin)*t*Real.exp ((p.supportExponent+margin)*k)
  have hh:=mul_le_mul_of_nonneg_left ex (Real.exp_pos (p.supportExponent*k)).le
  rw [add_mul,Real.exp_add,Real.exp_add]
  linarith only [hh]

omit [Fintype V] in
theorem complete_at (p:BudgetPoint) (D:ι→Support n) (F:ι→A→Poly Γ) {w:V→ℝ} {u margin:ℝ}
    (hw:∀v,0< w v) (H:Towed w D F p.B p.supportExponent u) (hmargin:0< margin) (small:u*blockSites p.B≤ margin/2) :
    ∃b:ι→ℝ,(∀i,0≤ b i ∧ ∀z,Poly.price w (F i z)≤ b i) ∧
      ∀Y:Support n,SumBudget (dirty p D Y b) ((2/margin)*(u*blockSites p.B)*Real.exp ((p.supportExponent+margin)*coverNumber p.B Y)) := by
  obtain ⟨b,_,hit,asset⟩:=H
  have point i:0≤ b i ∧ ∀z,Poly.price w (F i z)≤ b i:=by
    obtain ⟨sheet,np,has,price⟩:=asset i
    have nn (s:Γ.Mode):0≤ Poly.toll w s:=Finset.prod_nonneg (fun v _=>(hw v).le)
    refine ⟨(Finset.sum_nonneg (fun s _=>mul_nonneg (nn s) (np s))).trans price,fun z=>?_⟩
    exact (Finset.sum_le_sum (fun s _=>mul_le_mul_of_nonneg_left (has z s) (nn s))).trans price
  refine ⟨b,point,fun Y=>touching_at p D hmargin (fun i=>(point i).1) ?_ small Y⟩
  intro y
  convert hit y using 1
  funext i
  unfold BudgetPoint.mass
  split_ifs <;> ring

omit [Fintype V] in
theorem source_at (p:BudgetPoint) (D:ι→Support n) (F:ι→A→Poly Γ) {w:V→ℝ} {u c margin:ℝ}
    (hw:∀v,0< w v) (H:Towed w D F p.B p.supportExponent u) (hmargin:0< margin) (small:u*blockSites p.B≤ margin/2)
    (Y:ℕ→Support n) (stem:ℕ→ℝ) (pos:∀i,0≤ stem i)
    (paid:SumBudget (fun i=>stem i*Real.exp ((p.supportExponent+margin)*coverNumber p.B (Y i))) c) :
    ∃b:ι→ℝ,(∀i,0≤ b i ∧ ∀z,Poly.price w (F i z)≤ b i) ∧
      SumBudget (fun t:ℕ×Finset ι=>stem t.1*dirty p D (Y t.1) b t.2) ((2/margin)*(u*blockSites p.B)*c) := by
  obtain ⟨b,unit,partners⟩:=complete_at p D F hw H hmargin small
  have hu:0≤ u:=budget_nonneg (H.choose_spec.2.1 0)
  have ht:0≤(2/margin)*(u*blockSites p.B):=by exact mul_nonneg (div_nonneg (by norm_num) hmargin.le) (mul_nonneg hu (by unfold blockSites; positivity))
  refine ⟨b,unit,?_⟩
  apply budget_rows _ (fun i=>((2/margin)*(u*blockSites p.B))*(stem i*Real.exp ((p.supportExponent+margin)*coverNumber p.B (Y i))))
    _ (budget_scale ht paid)
  intro i
  convert budget_scale (pos i) (partners (Y i)) using 1
  ring

omit [Fintype V] in
theorem source (p:BudgetPoint) (D:ι→Support n) (F:ι→A→Poly Γ) {w:V→ℝ} {u c:ℝ}
    (hw:∀v,0< w v) (H:Towed w D F p.B p.supportExponent u) (small:u*blockSites p.B≤1/2)
    (Y:ℕ→Support n) (stem:ℕ→ℝ) (pos:∀i,0≤ stem i)
    (paid:SumBudget (fun i=>stem i*Real.exp ((p.supportExponent+1)*coverNumber p.B (Y i))) c) :
    ∃b:ι→ℝ,(∀i,0≤ b i ∧ ∀z,Poly.price w (F i z)≤ b i) ∧
      SumBudget (fun t:ℕ×Finset ι=>stem t.1*dirty p D (Y t.1) b t.2) (2*(u*blockSites p.B)*c) := by
  simpa only [div_one] using (source_at p D F hw H (show (0:ℝ)<1 by norm_num) small Y stem pos paid)

end YM.Integration.QLocalMarkedTouchingPrice
