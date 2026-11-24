import YM.QuadraticLocal.Relative.Curtain
import YM.QuadraticLocal.Germ.Harper
/-!
# Append-only Mask-preserving ψ cut for `Tint` reports

Uses sum-log pieces, no cancellation-based vacancy. Permit Holder.Taut
 etc for re-production. Proof from conditional hW(St...) dual ledger of
 the Splice caller. Never deleting any activated Mark on the realization;
 Crop is for statements on the Led and for aligning precise model sector.
 `mixture` reassigns costs.After last mutation & all concrete masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Deletion
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {T J ι μ η : Type} {w : V → ℝ} {a α β γ k b r Rk :ℝ} {B : ℕ}
variable {P : ℕ→ ForcedAddress G n} {F : Code G n} (S:Set V) (hw:∀ i,0<w i)
variable (H: Lamps T J G p o R)(U:Lamps T μ G p o R)
-- direct complement MAY fail to annihilate quiet if unsupported.U don’t establish ring hom!
def trash : Lamps T J G p o R:= { H with
   nominal t i:= if preserve (H.mode i).val S then 0 else H.nominal t i
   legal t i:=by split; exact regular_const _; exact H.legal t i
   pure t i _ ht:=by split; rfl; exact H.pure t i _ ht }
lemma about (h:H.Paid w B a b) : (trash S H).Paid w B a b:=by
   obtain ⟨f,hf,hH,hP⟩:= h.budget; refine ⟨f,hf,?_,hP⟩; intro i t x hx; unfold trash; dsimp only; split; exact bound_weaken (bound_const _) (norm_zero.trans_le (hf _)); exact hH i t x hx
-- Literal gauges.U.`. re-expression in original lights
local notation "Ψ"=> Deletion.crop R S
lemma trash_frame (i:J)(t:T)(U:Config G n): (trash S H|>.frame i t U)= H.frame i t U - (sink S H).frame i t U:=by
    rw [Deletion.frame]; unfold Lamps.frame; rw [Deletion.forever]; unfold trash Lamps.light; dsimp only [trash,Lamps.ground]; by_cases hp: preserve (H.mode i).val S
    · simp_rw [if_pos hp,sub_self]; split; rw [Pi.zero_apply,Poly.send_zero]; change Poly.send _ _=0; rw [show (masked p.threshold _ 0 U)= (0:ℂ) from ?_]; rw [Poly.send_zero]; unfold RG.masked; simp
    simp_rw [if_neg hp,Poly.send_zero,sub_zero]
include hw
lemma proceeds (h:H.Paid w B a b)(ha:0 ≤ a)(t:T)(U:Config G n): (sink S H).log t U=Ψ (H.log t U):= by unfold Lamps.log; rw [(Ψ).map_tsum (h.sums ha hw ..)]; exact tsum_congr fun i=> frame S H i t U
lemma litter (h:H.Paid w B a b)(ha:0 ≤ a)(t:T)(U:Config G n): (trash S H).log t U= H.log t U-Ψ (H.log t U):= by
    rw [← proceeds S hw H h ha]; unfold Lamps.log; simp_rw [trash_frame]; exact Summable.tsum_sub (h.sums ha hw ..) ((owed S H h).sums ha hw ..)
omit hw
lemma merge : sink S (H.join U)= (sink S H).join (sink S U):=by unfold sink Lamps.join; congr 1; funext t i; cases i <;> rfl
-- project keeps emitted signs.S.Persistence
lemma killed (t:T)(i): (sink S (trash S H)).nominal t i=0:= by by_cases hi: preserve (H.mode i).val S <;> simp only [sink,trash,hi,↓reduceIte]; rfl
lemma deduce : sink S (H.shade)=(sink S H).shade:=by
   unfold sink Lamps.shade; congr 1; funext t i; dsimp only; split; exact rfl; exact (neg_zero).symm
lemma own : sink S (sink S H)= sink S H := by unfold sink; congr 1; funext t i; dsimp only; split <;> rfl
local notation "R0"=> sink S H
lemma freed : (sink S (trash S H)).Paid w B a 0:=by
    refine ⟨fun _=>0, fun i=> le_rfl, fun i t x hx=>?_ ,fun i=>?_⟩
    · rw [killed]; exact bound_weaken (bound_const (0:ℂ)) (norm_zero.le)
    simp_rw [mul_zero,zero_mul,ite_self]; exact Extra.Multi.Budget.zero le_rfl
-- analytic U_model not affected. Keep all its tainted sectors: assign the actual post-calibrated
-- Born for the next step. Subtract tag-clean unsafe sectors as rough errors with the reference estimates.Enrollment.E.M. Upper not at the queried α factor level until using in lift.
variable (M:Lamps T ι G p o R) -- R0 raw; U clean old; M model
def mixture : Lamps T (μ⊕(J⊕ι)) G p o R:= (sink S U).join ((trash S H).join (trash S M).shade)
variable (hH:H.Paid w B a α)(hU:U.Paid w B a β)(hM:M.Paid w B a γ)
include hH hU hM
local notation "Tp"=> mixture S H U M
lemma prize : Tp|>.Paid w B a (β+(α+γ)):= Lamps.joinPaid (owed S U hU) (Lamps.joinPaid (about S H hH) (Lamps.expenseShade _ _ (about S M hM)))
lemma clean_prize : (sink S Tp).Paid w B a β:=by
   unfold mixture; rw [merge, own, merge, deduce]; simpa only [add_zero] using! Lamps.joinPaid (owed S U hU) (Lamps.joinPaid ( freed (w:=w) (B:=B) (a:=a) S H ) (Lamps.expenseShade _ _ (freed (w:=w) (B:=B) (a:=a) S M)))
include hw
-- equation before charging ANY ShiftRows.Soap changes.Sp representatives distinct from Clean solver's choice but re-expression at all fields.Model. require s at all.
variable (D':Canopy.ShiftRows T η G p o R)
local notation "φ"=> Canopy.ShiftRows.log D'
-- can crop `Sh` as ring map; keep Costs and Stencil.
def glow : Canopy.ShiftRows T η G p o R:={ D' with
   soap t i u:= Ψ (D'.soap t i u)
   cost t i:= by
     let h:= D'.cost t i; refine ⟨ fun a U=> congr_arg (Ψ) (h.gauge a U), (Ψ).continuous.measurable.comp h.borel,fun U V hx ht=> congr_arg (Ψ) (h.reads U V hx ht),fun U ν hH v hv=> h.carry U ν ?_ v hv⟩; contrapose! hH; rw [watching,hH,ite_self]
   clean t i U he:= D'.clean _ _ U (fun h=> he (by rw [h];exact (Ψ).map_zero))
   skip t i U:= (Deletion.quiet S _).trans (D'.skip t i U)
   single t i U:= by rw [← show (Ψ) ( (D'.soap t i U) * (D'.soap t i U) )= Ψ (D'.soap t i U) * Ψ (D'.soap t i U) from ModeWeight.rum R _ _ _, D'.single, (Ψ).map_zero] }
omit hH hU hM
lemma mood (h:D'.Budget w B a k): (glow S D').Budget w B a k:= by
   obtain ⟨f,hf,hG⟩:= h.earned; refine ⟨fun i=> Ψ (f i),fun i t U=>Deletion.cover S _ _ (hf i t U),fun i=> budget_mono (hG i) ?_ ?_⟩
   · intro j; split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
   intro j; dsimp only [glow]; split; exact mul_le_mul_of_nonneg_right (Deletion.paid _ hw _) (Real.exp_pos _).le; exact le_rfl
variable [Countable η][Fintype V] {w':V→ℝ}{B' : ℕ}
local notation "Ŵ"=> glow S D'
omit hw in
lemma aglow (h:D'.Budget w B a k)(ha:0≤a)(hw:∀ i,0<w i)(t:T)(U:Config G n): (Ŵ).log t U=Ψ (D'.log t U):=by unfold Canopy.ShiftRows.log; rw [(Ψ).map_tsum (D'.earnings h hw ha ..)]; rfl
include hH hU hM hw
lemma proceedsLux (ha:0≤a)(hV:D'.Budget w' B' r k)(hw':∀ i,0<w' i)(hb:0≤r)(t:T)(X:Config G n)(he:Ψ (H.log t X)= Ψ (M.log t X+U.log t X+(φ t X))):
   H.log t X=( M.join (mixture S H U M)).log t X+(glow S D').log t X:= by
    have ht:= hH.sums ha hw t X; have hm := hM.sums ha hw t X; let H':= trash S H; let U':= sink S U; have hU':= owed S U hU; let M':= (trash S M).shade; let V':= H'.join M'; have hv:= about S H hH; have hZ:=Lamps.expenseShade _ _ (about S M hM); have ht':= Lamps.joinPaid hv hZ; rw [aglow S D' hV hb hw' t X, mixture,Lamps.joinLog t X hm (( Lamps.joinPaid hU' ht').sums ha hw t X), Lamps.joinLog t X (hU'.sums ha hw ..) (ht'.sums ha hw ..), Lamps.joinLog t X (hv.sums ha hw ..) (hZ.sums ha hw ..), proceeds S hw U hU ha, litter S hw H hH ha, Lamps.shade_log, litter S hw M hM ha, he, (Ψ).map_add, (Ψ).map_add]; -- ha missing one
    abel
-- proof ORIENTATION
omit hH hU hM hw [Countable η] [Fintype V]
section dance
variable {E:V→Type} [∀ i,AddCommGroup (E i)][∀ i,Module ℝ (E i)]
variable (K: ∀ i,Submodule ℝ (E i)) (A:∀ i, Set (E i))
open Affinity
variable {H:Lamps (Wallet A) J G p o R} {U:Lamps (Wallet A) μ G p o R} {M:Lamps ( Wallet A ) ι G p o R}
variable {Φ:V→Support n}{D':Canopy.ShiftRows (Wallet A) η G p o R}
lemma desire (h:Taut Φ A K H): Taut Φ A K (sink S H) ∧ Taut Φ A K (trash S H):= by
    refine ⟨⟨h.house,fun i t=>?_⟩,⟨h.house,fun i t=>?_⟩⟩
    · unfold sink; simp only; split; exact h.adv i t; exact Attn.silent
    unfold trash; simp only; split; exact Attn.silent; exact h.adv i t
lemma favorite (h:Taut Φ A K H)(hv:Taut Φ A K U)(hm:Taut Φ A K M) : Taut Φ A K (mixture S H U M):=
    Affinity.Polish.Static.spawn (desire S K _ hv).1 (Affinity.Polish.Static.spawn (desire S K _ h).2 ( Affinity.Polish.Static.lunar (desire S K _ hm).2))
lemma glow_book (h:∀ i U', Affinity.Stencil Φ A K ((D'.place i).val) (fun t=>D'.soap t i U')) (i:η) (U':Config G n): Affinity.Stencil Φ A K ((D'.place i).val) (fun t=> (glow S D').soap t i U'):=by
    refine ⟨fun j =>?_⟩; unfold glow; simp_rw [Deletion.watching]; split; exact (h i U').each _; exact Addressable.gone
end dance
end YM.QuadraticLocal.Deletion
