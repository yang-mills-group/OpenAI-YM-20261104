import YM.OPE.Mountains.River
import YM.OPE.Mountains.Payout
import YM.OPE.Subpower
/-!
# Phase and full joint accounting
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Mountain
open Function Filter Finset Real OPE.Log
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} (hP:P.Coherent)
variable (H:Services C F S) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (hf:φ ≤ F.fuse)
    {W r d}(V:LogPackage C W r d) (hG:MatrixTicket (C:=C) S U.sector.derivatives φ)
variable {I J K:Type}[Fintype I][Fintype J] {s:Arboreal I} {χ:Ultrafilter K} {t:I→ℝ}
    {x:K→I→ E4}{R:K→I→ℝ}{M δ:ℝ}{i j k o:I} {a b : Finset I} {Y:K→J→E4}
    (L:K→Viewers U) (p:I→ C.book.Token) (q:J→ C.book.Token)(n:ℕ)(D:I→ℕ)(w:Mode U.sector.derivatives)
variable (h:s.Coterie (χ:Filter K) t M δ x R) (he:Backdrop (χ:Filter K) (fun i=> x i s.root) Y)
local notation "T!"=> (fun i=>s.fullLife (R i))
local notation "u!"=> (fun j n=> s.fee p (R j) s.leaves s.root n)
local notation "g!"=> (fun j=> groundError U P n (crop (x j) s.leaves) (crop p s.leaves) (x j s.root) (Y j) q)
private lemma prize (f:U.α.unselected.algebra): ∃ v: Viewers U, ‖f‖ ≤ 2*‖glance U v f‖:=by
    by_cases hh:‖f‖>0
    · by_contra! h; have hf: ‖f‖ ≤ ‖f‖/2:= (glance_contract U (by positivity)).mpr (fun i=> by linarith only [h i]); linarith only [hh,hf]
    exact ⟨none, le_trans (le_of_not_gt hh) (by positivity)⟩
include hf V hG hP H h he
lemma limelight : Wallet (χ:Filter K) T! (fun i=> u! i (n+1)* ‖g! i‖):=by
    choose L hL using fun i:K=> prize U (g! i); have hx:= all_flux U hP H hf V hG L p q n h he; apply ((Wallet.const h.time (2:ℝ)).mul hx.norm).of_est
    filter_upwards [overall_injected h he s.Action,root_inject h he,(fee_is p (n+1) h s.leaves s.initial).pos] with i hi hu hz; let E i':=flux P (spectator U (L i)) s.leaves (x i) p s.root (Y i) q i'; let c':= u! i (n+1); have hp':‖g! i‖ ≤ 2*‖E n‖:=by rw [show E n= _ from (glance_terms U P n (crop (x i) s.leaves) (crop p s.leaves) (x i s.root) (Y i) q (L i) hi hu).symm]; exact hL i
    rw [Real.norm_of_nonneg (mul_nonneg hz.le (norm_nonneg _)), norm_smul, Real.norm_of_nonneg hz.le]; change c'*_ ≤ 2*(c'* ‖E n‖); nlinarith only [mul_le_mul_of_nonneg_left hp' (show 0 ≤ c' from hz.le)]

omit hf V hG hP H h he

structure LogRate (s: Arboreal I)(P:Prescription U.sector.derivatives)(ξ:Mode U.sector.derivatives)(v:I→C.book.Token)(D:I→ℕ)(x:I→E4)(r:I→ℝ)(k:ℕ) : Prop where
    lifetimes : s.Qualified U P ξ x
    direct : ‖coalesce P s.leaves x v s.root ξ‖ ≤ s.listPrice v r ξ.1 k
    combination : ‖coalesce P s.leaves x v s.root ξ-factorization P s s.zones x v ξ D‖ ≤ s.listPrice v r ξ.1 k*s.grace r D
structure LogError (s:Arboreal I)(P:Prescription U.sector.derivatives)(p:I→ C.book.Token)(q:J→ C.book.Token)(n:ℕ)(x:I→ E4)(r:I→ℝ)(y:J→E4)(k:ℕ): Prop where
    right : Injective (beside (crop x s.leaves) y)
    apertures : Injective (beside (sole (x s.root)) y)
    ready : Tested U P n (crop x s.leaves) (crop p s.leaves) (x s.root) y q (s.listPrice p r (n+1) k)
include hf V hG hP H h
lemma bill : ∃ p':ℕ, ∀ᶠ j in χ, ∀ i:ℕ,i≥p'→ LogRate U s P w p D (x j) (R j) i:=by
    obtain ⟨b,hb⟩:= throughout U hP H hf V hG p w h s.Action; have hx:= whole_fuel D h; obtain ⟨c,hc⟩:= fullNest U hP H hf V hG p D w h s.Action hx; refine ⟨max b c,?_⟩
    filter_upwards [hb,hc,h.space,(run_towards h.collapse).eventually_ge_atTop 1,qualified (P:=P) U w h] with i hb hc h' he hz k hk; have hp:= h'.sizes; have hl:= hp.fee_pos (b:=s.leaves) p w.1 s.initial; change ‖u! i w.fst • coalesce P s.leaves _ p s.root _‖ ≤ _ at hb; rw [norm_smul,Real.norm_of_nonneg hl.le] at hb
    refine ⟨hz,hp.max_cost w.1 p he ((le_max_left ..).trans hk) hb,?_⟩
    by_cases hh:s.middle s.zones=∅
    · unfold leaves; rw [Nest.staging P (x i) w s.Action hh,sub_self,norm_zero]; simp [grace,hh]
    have hu:= hp.awards D (nonempty_iff_ne_empty.mpr hh); let F':=coalesce P s.leaves (x i) p s.root w-factorization P s s.zones (x i) p w D; apply (div_le_iff₀ hu).mp; apply hp.max_cost w.1 p he ((le_max_right ..).trans hk); rw [norm_smul] at hc; change ‖s.fee p (R i) s.leaves s.root w.1 * (s.grace (R i) D)⁻¹‖ * ‖F'‖ ≤ _ at hc; rw [Real.norm_of_nonneg (mul_pos hl (inv_pos.mpr hu)|>.le)] at hc; refine (Eq.trans_le ?_ hc); unfold F'; ring
include he
lemma stage : ∃ p':ℕ, ∀ᶠ j in χ, ∀ i:ℕ,i≥p'→ LogError U s P p q n (x j) (R j) (Y j) i:=by
    obtain ⟨b,hb⟩:= limelight U hP H hf V hG p q n h he; refine ⟨b,?_⟩; filter_upwards [hb,h.space,(run_towards h.collapse).eventually_ge_atTop 1,overall_injected h he s.Action,root_inject h he] with j hb he' ht hu hv k hk; exact ⟨hu,hv,tested U P n _ _ (x j s.root) (Y j) q (he'.sizes.max_cost (n+1) p ht hk ((Real.le_norm_self _).trans hb)) hu hv⟩
end YM.OPE.Arboreal.Mountain
