import YM.Qlocal.Provisional
/-!
# marker booking prices in tropical reserve
 Abbreviate relative currency by weight and envelope in the Peak's parameters.
One discount factor per MARK even though prepared from full modes. No comparing
coefficients by positive density. A discrepancy with multiplicative normalization
factor at a single name or a *stagewise admitted supermultiplicative envelope*
gets the appropriate factor on every allowed combination of names. Important:
 this doesn't purport to identify every input mode arising from lowering rank
 with a different COST if it is the *same* marker mode; use separate marker
 namespaces when transporting those discrepancies & their joins. Actual cost
 always tops envelope in the declared budget. Can choose weights already differing
 by name; stage parameters are global as quantised.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Emissions
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c c':R.Mode→ℝ}{k k' : ℕ}
    {a b d δ C A B θ ψ ψ₁ ψ₂:ℝ}
open Merge Switch UniformPays Publishing Payload Provisional

structure Spirit (f:R.Mode→ℝ):Prop where
 charge : ∀ {ι:Type} (q:ι→ R.Mode), Charge q f
namespace Spirit
variable (h:Spirit c)
include h
lemma light : c R.quiet=1:= (h.charge (fun _ : Unit=> R.quiet)).quiet
lemma fresh (x:R.Mode):0 < c x:= (h.charge (fun _:Unit=> x)).positive x
omit h
lemma tally (u:V→ℝ)(h:∀ i,0 < u i): Spirit (R:=R) (envelopeProduct u) := ⟨owed h⟩
lemma certain : Spirit (fun _ : R.Mode=>1):= by convert! tally (R:=R) _ (fun _=> zero_lt_one) using 1; ext i; simp [envelopeProduct]
end Spirit

/-- restore λ but keep make-good's relative factor.E.Note: inverse factor. -/
def rent (w:V→ℝ) (q:R.Mode→ℝ)(j:R.Mode):ℝ:=exchange (fun v=>(q v)⁻¹) w j
lemma rent_spend (h:∀ i,0<w i) (hp:∀ i,0<c i)(i:R.Mode):0<rent w c i:= mul_pos (Poly.worth h i) (inv_pos.mpr (hp _))
variable (ζ:V→ℝ)(η δ:ℝ) (X:ℝ)
/-- decrease in *radius norm parameter*, not a scale of test args. -/
def shift (x:ℝ)(u:V→ℝ)(i:V):ℝ:= u i / x
omit [DecidableEq V] in
lemma shift_pos {x:ℝ}(he:0<x)(hp:∀ i,0<w i)(i:V):0<shift x w i:= div_pos (hp _) he
omit [DecidableEq V] in
lemma shift_chain (u:V→ℝ) (v c:ℝ) : shift c (shift v u)=shift (v*c) u:= funext fun i=> div_div (u i) v c
lemma voyage (hp:∀ i,0≤c i)(hz:∀ i,0<u i)(j:R.Mode) (H:1 ≤ X)(h:j.val.Nonempty) : rent (shift X u) c j ≤ X⁻¹*rent u c j:= by
 unfold rent exchange; rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (hp j))
 unfold Poly.toll shift; simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const]; rw [mul_comm X⁻¹]; refine mul_le_mul_of_nonneg_left ?_ (Poly.worth hz j|>.le)
 have hv:(1:ℕ)≤ j.val.card:= Finset.card_pos.mpr h; exact le_trans (pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans H)) (inv_le_one_of_one_le₀ H) hv) (le_of_eq (pow_one _))
lemma nextkind (j:deck R s) : (kind j).val.Nonempty := by cases j with
    | inl j=> exact j.fst.val.2.prop
    | inr j=> exact j.fst.val.2.prop
-- Bridged price at prepared radius X≥1. Implies Brand and caption strut.
variable (h:Spirit c)(H:1 ≤ X)(hw:∀ i,0<w i)
local notation "u⌕"=> rent w c
local notation "z"=> shift X w
include h H hw
lemma health (g:ι→R.Mode) (U:Finset ι)(hu:Fits g U) :
   rent z c (unionTag g U hu) ≤ ∏ i∈U,rent z c (g i):= by
 have hy:= (h.charge g).joint _ hu; have hP i : 0 < Poly.toll z (g i):=Poly.worth (shift_pos (zero_lt_one.trans_le H) hw) _
 unfold rent exchange; simp_rw [prod_mul_distrib,prod_inv_distrib, toll_union]; exact mul_le_mul_of_nonneg_left (inv_anti₀ (prod_pos fun _ _=> h.fresh _) hy) (prod_pos fun i _=> hP i).le -- `lt`? 
lemma prepaid : Brand (marks (rent w c) X⁻¹ s) (rent z c) 1:= by
 apply Provisional.renewed (s:=s) (rent_spend hw h.fresh) (inv_pos.mpr (zero_lt_one.trans_le H)) zero_le_one
 intro U hv; rw [one_mul]; refine (health X h H hw kind U hv).trans (Finset.prod_le_prod (fun i _=> (rent_spend (shift_pos (zero_lt_one.trans_le H) hw) h.fresh _).le) (fun i _=> voyage X (fun i=>(h.fresh i).le) hw (kind i) H (nextkind _)))
omit H in
lemma recover (hp:1≤ X)(hx:∀ i:R.Mode,i.val.card ≤ k)(j : R.Mode) : rent w c j ≤ X^k*rent z c j:= by
 let v:= zero_lt_one.trans_le hp; unfold rent exchange; rw [←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (h.fresh _).le); unfold Poly.toll shift; simp_rw [div_eq_mul_inv,prod_mul_distrib,prod_const]; rw [mul_left_comm (X^k)]; apply le_mul_of_one_le_right (Poly.worth hw _|>.le); rw [inv_pow]; -- pay.A
 apply le_trans _ (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp (hx j)) (inv_nonneg.mpr (pow_nonneg v.le _)))
 rw [mul_inv_cancel₀ (pow_pos v _).ne']
end YM.Qlocal.Emissions
namespace YM.Qlocal.Publishing.Peak
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {o:V→Site n}{a b r A B X Y:ℝ} {c c':R.Mode→ℝ} {T:Taste Ω o P R}
variable (h₁:∀ i, 0 ≤ c' i) (h₂:0 ≤ X)
include h₁ h₂
private lemma up (p:Lattice.Side) (N:ℕ) (s:ι→Support p) (f : ι→ℝ) (q:ι→ R.Mode) (hu: Ac.Hit s N (fun i=> c (q i)*f i) a A) (hf:∀ i,0 ≤ f i) (hz:∀ i,c' (q i) ≤ X*c (q i)) : Ac.Hit s N (fun i=> c' (q i)*f i) a (X*A):= by
 intro x; refine budget_mono (budget_scale h₂ (hu x)) (fun i=> ?_) (fun i=>?_); · split; exact mul_nonneg (mul_nonneg (h₁ _) (hf _)) (Real.exp_nonneg _); rfl
 split
 next=> exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hz i) (hf i)) (Real.exp_nonneg _)) (le_of_eq (by ring))
 next=> rw [mul_zero]
variable [Nonempty Ω]
lemma transfer (h : Peak P o T c a A B)(hu : ∀ i:R.Mode,i.val.Nonempty→ c' i ≤ X*c i) : Peak P o T c' a (X*A) (X*B):= by
 let u:= h.active (Classical.ofNonempty); obtain ⟨f,hf,hQ,hV⟩:= h.regular; obtain ⟨s,hs,hY,hZ⟩:= h.captions; obtain ⟨y,hy,hT,hL,hB⟩:=h.forced; exact
    { h with regular:=⟨f,hf,hQ,up h₁ h₂ n _ _ _ T.menu.rays hV hf fun i=>hu _ (u.articles.proper i)⟩, captions:= ⟨s,hs,hY, up h₁ h₂ n _ _ _ T.tag hZ hs fun i=>hu _ (u.captions.card i)⟩, forced:= ⟨y,hy,hT,hL,up h₁ h₂ _ _ _ _ (fun i:ℕ×ℕ=>T.menu.marks i.1 i.2) hB hy fun i=>hu _ (u.articles.occurs i.1 i.2)⟩ }
omit [Nonempty Ω] h₁ h₂
lemma loosen (h: Peak P o T c a A B)(ha:A ≤ b) (hp : B ≤ r): Peak P o T c a b r:= by
 obtain ⟨f,hf,hQ,hV⟩:= h.regular; obtain ⟨s,hs,hY,hZ⟩:= h.captions; obtain ⟨y,hy,hT,hL,hB⟩:=h.forced; exact {h with regular:=⟨f,hf,hQ,fun i=>budget_loosen (hV i) ha ⟩, captions:= ⟨s,hs,hY, fun i=> budget_loosen (hZ i) ha⟩, forced:=⟨y,hy,hT,hL,fun i=>budget_loosen (hB i) hp⟩}
lemma nonneg (h : Peak P o T c a A B) : 0 ≤ A ∧ 0 ≤ B:= by obtain ⟨_,_,_,H⟩:= h.regular; obtain ⟨_,_,_,_,U⟩:= h.forced; exact ⟨ budget_nonneg (H 0), budget_nonneg (U 0) ⟩
end YM.Qlocal.Publishing.Peak
