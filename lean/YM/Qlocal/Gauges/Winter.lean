import YM.Qlocal.Gauges.Mastery
/-!
 Temporary currency and analytic customers vs error rows. Revenue on warming at ν.
 Do not require actual physical coefficients within radius regime. Project back after.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Parabola
open RGComparison01 RGComparison01.Pledge
open Quipu Quipu.Sonnet
open Atlas Planet
variable {Ω ι J V I : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n c:Side}{P: RG.Rep G n}
    {o:V→Site n}{s s':V→Support n}{q:Parabola.Ray R}{a b v t δ C A B θ ρ ζ:ℝ}{m k:ℕ}
namespace Revenue
variable [Fintype V] (p:Rental q) (f:Ω→Senses R→ℂ)(hz:0<δ) (hd:δ ≤1) (hu:1≤v)
-- Parameter v one common step cost f/. specialized lift. Input residual price δ>0. No theorem assuming size_it.years.
local notation "G₀"=> Loft R s
local notation "Dk"=> Payload.deck R s
local notation "Ψ"=>Planet.Whole G₀
set_option quotPrecheck false
local notation "B!"=> Live o R k
local notation "μ₁"=> tense
abbrev chip (q:Ray R)(v δ:ℝ)(s:V→Support n): Loft R s→ℝ := Sum.elim (Provisional.radius q (v⁻¹/δ) s) (fun _=>v⁻¹)
abbrev pour (j:Loft R s)(x:Ω):ℂ := Sum.elim Payload.valueH (f x) j
noncomputable def shift (q:Ray R)(v δ:ℝ)(f:Ω→ Senses R→ℂ)(s:V→Support n)(x:Ω)(j: Loft R s):ℂ:= pour f j x /↑(chip q v δ s j)
abbrev compile (q:Ray R)(v δ:ℝ)(s:V→Support n) (i:Stakeup R o s k):= chip q v δ s (intoK R s o k i)
local notation "hf!"=> chip q v δ s
local notation "S0"=> Revenue.shift q v δ f s
variable (hc:∀ x i,q (i:Senses R).val* ‖f x i‖ ≤ 1)
include p hu hz
lemma rising (i:G₀) : 0<chip q v δ s i:= by
 have ht:0<v⁻¹:=inv_pos.mpr (zero_lt_one.trans_le hu); rcases i with i|i; exact Provisional.price p.pos (div_pos ht hz) i; exact ht
lemma raised (x i): (↑(hf! i):ℂ)*S0 x i=pour f i x:=by unfold shift; field_simp [Complex.ofReal_ne_zero.mpr (rising p hz hu i).ne']
local notation "©"=> Atlas.slate R s
lemma costA (x:Ω)(i:Dk) : q (kind i)*‖S0 x (Sum.inl i)‖=δ * v:=by
 unfold shift; change _ * ‖Payload.valueH i/(Provisional.radius q _ s i:ℂ)‖=_; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg ((Provisional.price p.pos (div_pos (inv_pos.mpr (zero_lt_one.trans_le hu)) hz)) i).le]; rw [show ‖Payload.valueH i‖=1 from (by cases i <;> exact colour_norm _)]; unfold Provisional.radius; field_simp [(p.pos (kind i)).ne', hz.ne',(zero_lt_one.trans_le hu).ne'] <;> ring
include hd hc
lemma audition (i:Loft R s)(x:Ω): q (Atlas.slate R s i)* ‖S0 x i‖ ≤ v:=by
 cases i with
 | inl i=> change q (kind i)*_ ≤ _; rw [costA p f hz hu]; exact mul_le_of_le_one_left (zero_le_one.trans hu) hd -- include
 | inr i=> unfold shift; change q i.val* ‖f x i / (v⁻¹:ℝ)‖ ≤ _; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr (zero_lt_one.trans_le hu)|>.le),div_eq_mul_inv,inv_inv,←mul_assoc]; exact mul_le_of_le_one_left (zero_le_one.trans hu) (hc x i)
-- omit for earnings?
local notation "ι'"=> Atlas.Notice R
omit hc hd hu hz
omit [Fintype V] in
lemma buys (g:I→R.Mode) (u:Finset I)(hv:Fits g u): q (unionTag g u hv)≤∏ i∈u, q (g i):=by
 induction u using Finset.induction with
 | empty=> rw [Finset.prod_empty,show unionTag _ ∅ hv=R.quiet from Subtype.ext Finset.biUnion_empty]; exact p.zero.le -- p.zero proof q=1
 | insert i u hx hi=> let h:= hv.subset g (subset_insert ..); rw [Finset.prod_insert hx]; refine le_trans (p.multiply _ _ _ ?_) (mul_le_mul_of_nonneg_left (hi h) (p.pos _).le) -- name
                      refine ⟨(disjoint_biUnion_right ..).mpr (fun j hj=> hv.1 (mem_insert_self ..) (mem_insert_of_mem hj) (fun he=>hx (he.symm ▸ hj))), Finset.biUnion_insert.symm ⟩
section 
variable (g:Ω→ Loft R s →ℂ)
local notation "p★"=> Translation.stamp (Atlas.slate R s)
local notation "μ★"=> Translation.falls (Atlas.slate R s)
lemma leased (u:(Whole G₀).Mode) (h:Fits (Atlas.slate R s) u.val)(x:Ω): q (Translation.stamp (Atlas.slate R s) u)* ‖Translation.falls (Atlas.slate R s) (g x) u‖≤∏ i∈u.val,(q (Atlas.slate R s i)* ‖g x i‖):=by rw [Translation.stamp,dif_pos h,Translation.falls,if_pos h,norm_prod,prod_mul_distrib]; exact mul_le_mul_of_nonneg_right (buys p _ _ h) (prod_nonneg fun i _=> norm_nonneg _)
omit p in
lemma toll_blank (u:(Whole G₀).Mode)(h:¬Fits (Atlas.slate R s) u.val) (x:Ω): q (Translation.stamp (Atlas.slate R s) u)*‖Translation.falls (Atlas.slate R s) (g x) u‖=0:=by unfold Translation.falls; rw [if_neg h,norm_zero,mul_zero]
include hu hc hd hz in
lemma leaves (u:(Whole G₀).Mode) (x:Ω) : q (p★ u)* ‖μ★ (S0 x) u‖≤ v^u.val.card:=by
 by_cases h:Fits (Atlas.slate R s) u.val; swap; · rw [toll_blank S0 u h x]; exact pow_nonneg (zero_le_one.trans hu) _
 refine (leased p S0 u h x).trans ((Finset.prod_le_prod (f:=fun i:Atlas.Loft R s=> q (Atlas.slate R s i)*‖S0 x i‖) (g:=fun _=> v) (fun i _=>mul_nonneg (p.pos _).le (norm_nonneg _)) (fun i hi=>?_)).trans_eq (prod_const _)); exact audition p f hz hd hu hc i x -- syntax order
include hd hu hz hc in
lemma entrance (i:(Whole G₀).Mode)(x:Ω)(hi:i.val.Nonempty)(hp:i ∉ Set.range (Atlas.tag R s)): let w:=(Fintype.card V); q (p★ i)* ‖μ★ (S0 x) i‖≤ δ*v^w:=by
 let w:=(Fintype.card V); intro w'; by_cases h:Fits (slate R s) i.val; swap; · rw [toll_blank S0 i h x]; exact mul_nonneg hz.le (pow_nonneg (zero_le_one.trans hu) _)
 obtain ⟨j,hj⟩:= Atlas.rough (R:=R) (s:=s) i hp hi h; let i':= Sum.inl (α:=Dk) (β:=Senses R) j
 let u' a:= q (slate R s a)*‖S0 x a‖; have hc' a:0≤u' a:= mul_nonneg (p.pos _).le (norm_nonneg _)
 have h':u' i'=δ*v:=costA p f hz hu x j; apply (leased p S0 i h x).trans; change ∏ i∈_,u' i≤_; rw [← mul_prod_erase i.val u' (show i'∈_ from hj),h', mul_assoc]; apply mul_le_mul_of_nonneg_left _ hz.le; apply le_trans _ (pow_le_pow_right₀ hu (le_trans (grade_hunger (slate R s) hot0 i.val h) (Finset.card_le_univ _))); rw [← show ∏ _∈(i.val), v=v^i.val.card from prod_const _,← mul_prod_erase i.val (fun _=>v) hj]; exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>hc' i) (fun i _=> audition p f hz hd hu hc i x)) (zero_le_one.trans hu)
-- δ^arity refined paths of EVERY contribution at every res ticket even with two Error tags. Cost.Sea.Client.Trace.Year.Packet retains Φ.C.Price Epoch.Basis annotation.She.Selection.Future. `wsT = v^(-arity)` across symbols.λ interpreter factor after Epoch. Debug ν.Book.Ph.Power.
noncomputable def repay (V:Type)[Fintype V][DecidableEq V](v:ℝ):Ray (Whole V):=fun i=> v⁻¹^i.val.card
omit p [Fintype V] in
lemma receipt (W:Type)[Fintype W][DecidableEq W] (hu:1≤v): Rental (repay W v):=by
 have he:0<v⁻¹:=inv_pos.mpr (zero_lt_one.trans_le hu); refine ⟨fun i=>pow_pos he _,fun i j k h=>?_ , pow_zero _⟩ -- card quiet
 change v⁻¹^(k.val.card) ≤ _; rw [← h.2,Finset.card_union_of_disjoint h.1,pow_add]; rfl
end
end Revenue
end YM.Qlocal.Gauges
namespace YM.Qlocal.Gauges.Revenue
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Parabola
open RGComparison01 RGComparison01.Pledge
open Quipu Quipu.Sonnet Atlas Planet
variable {Ω ι J V I : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n c:Side}{P: RG.Rep G n}
    {o:V→Site n}{s s':V→Support n}{q:Parabola.Ray R}{a b v t δ C A B θ ρ ζ:ℝ}{m k:ℕ}
variable [Fintype V] (p:Rental q) (f:Ω→ Senses R→ℂ)(hz:0<δ) (hd:δ ≤1) (hu:1≤v)
local notation "G₁"=> Loft R s
set_option quotPrecheck false
local notation "Ψ"=>Planet.Whole G₁
local notation "q★"=> Atlas.slate R s
local notation "S0" => Revenue.shift q v δ f s
local notation "p0"=>repay G₁ v
local notation "z★"=>Palace.blank G₁
variable (hc:∀ x i,q (i:Senses R).val* ‖f x i‖ ≤ 1)
include p hu hz hd hc
lemma omega_regular : Translation.News (slate R s) (Revenue.shift q v δ f s) z★ q (v^(Fintype.card V)):= by
 intro i x; change _ ≤ v^(Fintype.card V)*1; rw [mul_one]; by_cases hm:Fits (slate R s) i.val; swap; · rw [toll_blank]; exact pow_nonneg (zero_le_one.trans hu) _; exact hm
 apply (leaves p f hz hd hu hc i x).trans (pow_le_pow_right₀ hu (le_trans (grade_hunger _ hot0 _ hm) (card_le_univ _)))
lemma omega_hard : Translation.News (slate R s) (Revenue.shift q v δ f s) (repay G₁ v) q (v^(2*Fintype.card V)):= by
 intro i x; let h:= receipt G₁ hu; have h0:0<v:= zero_lt_one.trans_le hu; by_cases hm:Fits (slate R s) i.val; swap; · rw [toll_blank]; exact mul_nonneg (pow_nonneg h0.le _) (h.pos _).le; exact hm
 apply le_trans (leaves p f hz hd hu hc i x); unfold repay; rw [inv_pow,← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos h0 _)).2; rw [←pow_add]; exact pow_le_pow_right₀ hu (by have h': i.val.card ≤ Fintype.card V:= le_trans (grade_hunger _ hot0 _ hm) (card_le_univ _); omega)
omit p hz hd hc
lemma aging (T:Type)[Fintype T][DecidableEq T]: repay T v ≤ Palace.blank T ∧ ∀ i:(Whole T).Mode,i.val.Nonempty→ repay T v i ≤ v⁻¹:= by
 have he :1 ≤ v:= hu; have ht:0 < v⁻¹:= inv_pos.mpr (zero_lt_one.trans_le hu); refine ⟨fun i=> pow_le_one₀ ht.le (inv_le_one_of_one_le₀ hu),fun i hi=>?_⟩
 exact le_trans (pow_le_pow_of_le_one ht.le (inv_le_one_of_one_le₀ hu) (show 1 ≤ i.val.card from Finset.card_pos.mpr hi)) (pow_one _).le
end YM.Qlocal.Gauges.Revenue
