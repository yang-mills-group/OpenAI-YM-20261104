import YM.MergeProof.Chalet
import YM.MergeProof.Montage
import YM.MergeProof.Sonata
import YM.Extra.MULTISOURCE_BOUNDS.Forest
/-!
# One more posthistory regular reserve

Strengthen Book purchases before manufacturing the Family, not by comparing two
choices of its birth terms. Use DECK (reserved +2 mass) while `Tare` still
meets bookings for the same forced terms. This is NOT an improvement on the
numerical power losses transferred down each step.

Adapted from `YM/Planned/ATOM_GUARDED_LAYOUT/{Guards,Intake,Orbit}` and
`YM/MergeProof/{Chalet,Montage}`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {d:ℕ} {n:Side} {R:Rep G n} {Y: Hol G}
   {F:Labels.Frame G d} {P:Coefficient F n} {M:Local.Raw F n}{o y: Site n} {b:ℕ→Support n}
   {B:SectionData F} {σ C Λ δ w κ a e:ℝ}

def Blown (P : Coefficient F n)(o:Site n)(R:Rep G n)(a:ℝ) :=
    ∃ e : ℕ→ℝ, SumBudget (fun i=>reservedMass R.p (P.support i) (e i)) a ∧
    ∀ i, R.p.supBounds o (P.support i) (P.regular i) (e i)
namespace Blown
variable (h:Blown P o R a)
include h
lemma price : 0≤ a := by obtain ⟨e,hE,hB⟩:=h; exact sumBudget_credit hE
lemma enlarge (hx:a≤C) : Blown P o R C:=by obtain ⟨e,hE,hB⟩:=h; exact ⟨e,⟨hE.1,hE.2.1,hE.2.2.trans hx⟩,hB⟩
lemma bar (hf : P.Format o Y R) : Blown (barAll P) o R a:=by
   obtain ⟨e,hE,hB⟩:=h; exact ⟨e,hE,fun i=>bound_bar (hf.smooth i) (hB i)⟩
lemma turn {s:Signed} (m:R.activities.Moves s y)(hf : P.Format o Y R):
    Blown (reorient m P) (affine s y o) R (turnCost R.p.order R.p.power*a) := by
   let t:=turnCost R.p.order R.p.power; obtain ⟨e,hE,hB⟩:=h
   refine ⟨fun i=>t*e i, ?_,fun i=>bound_pull (hf.smooth i) (hB i) s y⟩
   have ht:0≤t:=pow_nonneg (by positivity) _
   simpa only [t,reorient,reservedMass,cover_map _ (turn_sep s y),mul_left_comm _ (turnCost R.p.order R.p.power)] using sumBudget_mul_left hE ht
lemma spin {z:Extra.Histories.Motion}(S : R.activities.Moves z.1 y)(hf:P.Format o Y R)(hn:2≤ n.val) : Blown (audition S P) (affine z.1 y o) R (turnCost R.p.order R.p.power*a):= by
   have ht:= turn h S hf; unfold audition; split; exact ht.bar (format_reorient S hf hn); exact ht
lemma stretchable (c:ℂ): Blown (Extra.Histories.stretch c P) o R (‖c‖*a):= by
  obtain ⟨e,hE,hB⟩:=h; refine ⟨fun i=>‖c‖*e i, ?_, fun i=> bound_smul _ (hB i)⟩
  simpa only [Extra.Histories.stretch,reservedMass,mul_left_comm _ ‖c‖] using sumBudget_mul_left hE (norm_nonneg c)
omit h
lemma joins {ι: Type*}{P:ι→ Coefficient F n}{a:ι→ℝ} (e : ℕ≃ι×ℕ)(h:∀ i, Blown (P i) o R (a i))(hp:Summable a): Blown (Extra.Histories.merge e P) o R (∑' i,a i):= by
   choose E he hQ using h; let f (x:ι×ℕ):= reservedMass R.p ((P x.1).support x.2) (E x.1 x.2); have hm:= budget_prod (f:=f) he hp; exact ⟨fun i=> E (e i).1 (e i).2,⟨fun i=>hm.1 _,hm.2.1.comp_injective e.injective,(e.tsum_eq f).trans_le hm.2.2⟩,fun i=>hQ ..⟩ -- '..' prop issue
lemma pencil_joins {ι:Type*}[Fintype ι]{P:ι→ Coefficient F n}{a:ι→ℝ} (e : ℕ≃ι×ℕ)(h:∀ i, Blown (P i) o R (a i))(w:F.Coeff→ₗ[ℂ] ι→ℂ)(u:F.Coeff): Blown (Extra.Histories.pencil e P w u) o R (∑ i,‖w u i‖*a i):=by simpa only [tsum_fintype] using! joins e (fun i=> (h i).stretchable (w u i)) (Summable.of_finite)
lemma primary (x:F.Coeff)(ht:0≤σ): Blown (Extra.Histories.primary o x) o R σ:=by
   refine ⟨0, ?_,fun i=>?_⟩; simp_rw [Pi.zero_apply,reservedMass,mul_zero]; exact sumBudget_zero ht
   exact Extra.Multi.supBounds_zero ..
lemma deck (S : Berths R.p R.activities (fun i=>joint B o (b i)))
    (hf : M.Format o b R)(he:Readable Y B R.p n w) (ha : Planned.GuardedAtom.Deck M o b R κ a e) : Blown (mint S M Y) o R (factor Y B R.p.supportExponent w *a):=by
   obtain ⟨p,hP,hQ⟩:= ha.bulk; let F' i:=joint B o (b i); let t i:=atomPrice Y F w*p i; let C':=factor Y B R.p.supportExponent w; have ht:0≤ C':= mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (atomPrice_ge_one Y F he.nonneg)); have hp(i) := (charge_atom o he (hf.regular i) (hP i)).1
   refine ⟨t,?_ ,fun i=>hp i⟩; apply sumBudget_mono (sumBudget_mul_left hQ ht) _ _ le_rfl
   · -- remaining goals inspect
     exact fun i=> mul_nonneg (Real.exp_pos _).le (hp i).1
   intro i; exact price_join B Y o (hf.origin i) he.sound he.nonneg (hP i).1
end Blown
end YM.MergeProof
