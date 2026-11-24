import YM.OPE.Vitrines.Funding
import YM.OPE.Yarn.Custom
import YM.MergeProof.North.Jazz
/-!
# Stored membrane and error coupons for B vs scene
Each proxy `enamel` will be read later on the *same k mesh*. Depends on actual
(local representative!) nonanalytic entries; no approximation by germs claimed. On
restoring errors keep every single and every mixed budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Vitrines
open Lattice Wilson RG Function Filter Set MeasureTheory Marker Push
open MergeProof Accent Ribbons ManyCopies MergeProof.Float Source Labels Extra.Histories Next Next.UVStress
open Extra.Multi Planned.GuardedAtom Local PhysicalNext.Repeat Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{n:Side}{σ C Λ δ w ρ θ:ℝ}
variable {D:Labels.Frame G d}(S:SectionData D)(R:Rep G n)(P:Coefficient D n)
local notation "𝒞"=> Config G n
local notation "x₀"=> (0:Site n)
local notation "t"=> R.p.threshold
local notation "B"=> R.p.B
local notation "X"=> P.support

/-- Color here: not color input rem.DO NOT truncate V's mask. -/
def height (i:ℕ):= coverNumber R.p.B (P.support i)
def relict (v:𝒞)(i:ℕ)(r:ℕ):= if r≤height R P i then P.maskedTerm R i v else 0
def drift (r:ℕ)(v:𝒞):= ∑' i,relict R P v i r
def enamel (r:ℕ) (v:𝒞):= P.exponentialEntry 0 S R v - drift R P r v
-- use as replacement also analytic f+θ.U lots
private lemma suppliesC {X':Support n}{v:ℝ}{f:Config G n→ℂ}{p:BudgetPoint}{o:Site n}(ht:p.Regular X' f)(hp:p.supBounds o X' f v):
    let F:=masked p.threshold X' f; GaugeInvariant F ∧ Measurable F ∧ UsesFinal p.threshold X' F ∧ (∀ u, F u≠0 →Healthy p.threshold X' u)∧ ∀ u,‖F u‖≤v:=by
   intro F; refine ⟨Rank.Alarm.sails _ _ _ ht.symmetry, masked_measurable _ _ _ ht.borel,fun U V huv h=>?_,fun u h=> by_contra fun H=>h (masked_ne _ _ _ _ H),fun u=>?_⟩
   · unfold F; have hc:Healthy p.threshold X' U↔ Healthy p.threshold X' V:=by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,h]
     by_cases he : Healthy p.threshold X' U; · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (hc.mp he)]; exact ht.sites _ _ huv
     rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (mt hc.mpr he)]
   unfold F; by_cases h:Healthy p.threshold X' u; · rw [masked_eq _ _ _ _ h]; exact hp.2 u h [] (Nat.zero_le _) (by simp)
   rw [masked_ne _ _ _ _ h,norm_zero]; exact hp.1

variable {P R}
lemma drifts (A:Menu.Arsenal R){Y:Hol G} (he:P.Format x₀ Y R) (h: Blown P x₀ R C)(r:ℕ) : Blade R x₀ (drift R P r) 0 0 (2*(Real.exp (-(2:ℝ)*r)*C)):=by
    obtain ⟨x,hx,hX⟩:= h; let F i U:= relict R P U i r; let v i:= if r≤height R P i then x i else 0; let s:= Real.exp (-(2:ℝ)*r); have h r:=Real.exp_pos (-(2:ℝ)* (r:ℕ));
    have hk i : GaugeInvariant (F i) ∧ Measurable (F i) ∧ UsesFinal t (X i) (F i) ∧ (∀ U,F i U≠0→Healthy t (X i) U)∧ ∀ U, ‖F i U‖ ≤ v i:=by
       unfold F v relict; split_ifs; exact suppliesC (he.smooth _) (hX _)
       exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _=>rfl,fun u h=>False.elim (h rfl),fun _=>(norm_zero).le⟩
    refine carriage A F X (fun i=>(hk i).1) (fun i=>(hk i).2.1) he.origin (fun i=>(hk i).2.2.1) (fun i=>(hk i).2.2.2.1) (g:=v) (fun i=>(hk i).2.2.2.2) ?_
    apply Local.sumBudget_mono (Local.sumBudget_mul_left hx (h r|>.le)) _ _ le_rfl
    · intro i; apply mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans ((hk i).2.2.2.2 1))
    intro i; unfold BudgetPoint.mass v reservedMass; dsimp only; split_ifs with hf
    · rw [← mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) (hX i).1
      have he : (r:ℝ) ≤ ↑(coverNumber R.p.B (X i)):= by exact_mod_cast hf
      linarith only [he]
    rw [mul_zero]; exact mul_nonneg (h r|>.le) (hx.1 _)
private lemma impure (A:Menu.Arsenal R){Y:Hol G} (he:P.Format x₀ Y R)(ht:P.remBound x₀ R ρ C) : Blade R 0 0 (profile R.activities P.forced) 0 (2*ρ*C):=by
    obtain ⟨a,b,he',hf,hg,h₀,hT,hC⟩:=ht; have hK:2*(ρ*b)≤2*ρ*C:= by rw [mul_assoc (2:ℝ)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [he',hg]) h₀.le) zero_le_two
    apply (punch A (show Local.ForceFormat R.p R.activities 0 P.forced from ?_) (show ForceCost R.p R.activities P.forced (ρ*b) from hC)).more hK
    constructor <;> first|exact he.forcing|exact he.carried|exact he.invariant|exact he.supported|exact he.borel
-- enamel chosen: tails (r=B eventually).
lemma silver (A:Menu.Arsenal R){Y:Hol G} (he:P.Format x₀ Y R)(ht:P.remBound x₀ R ρ C)(h: Blown P x₀ R C)(r:ℕ):
    Blade R 0 (P.exponentialEntry 0 S R - enamel S R P r) (profile R.activities P.forced) 0 (2*(Real.exp (-(2:ℝ)*r)+ρ)*C):=by
    have hh:= (drifts A he h r).comp (impure A he ht); rw [add_zero,zero_add,add_zero] at hh; convert hh using 1; · funext U;dsimp [enamel]; abel
    ring
lemma gold (A:Menu.Arsenal R){Y:Hol G} (he:P.Format x₀ Y R)(ht:P.remBound x₀ R ρ C)(h:Blown P x₀ R C)(hq:x₀∈ S.footprint (0:Site n)) (hy:∀ i:D.Index, R.p.Regular (S.footprint (0:Site n)) (S.places (Pi.single i 1) 0)∧R.p.supBounds 0 (S.footprint (0:Site n)) (S.places (Pi.single i 1) 0) (δ*R.p.threshold ^(D.grades i).2)) :
 Blade R 0 (P.exponentialEntry 0 S R - (fun _=> P.x 0)) (profile R.activities P.forced) 0 (2*(R.p.mass (S.footprint (0:Site n)) (δ*D.coeffSize (D.core P.x))+(1+ρ)*C)):= by
    have h:= silver S A he ht h 0; let X':= S.footprint (0:Site n); let F:= masked t X' (S.places (D.scaled (t)⁻¹ (D.core P.x)) 0); obtain ⟨h1,h2,h3,h4,h5⟩:= suppliesC (show R.p.Regular X' _ from (BasisCost.analytic S R.p (D.core P.x) 0 hy).1) (BasisCost.analytic S R.p (D.core P.x) 0 hy |>.2)
    have hX:= MergeProof.Float.petals A X' F h1 h2 h3 h4 (fun _=>hq) h5 -- f repeated
    have hh:= hX.comp h; rw [zero_add,zero_add] at hh; convert hh using 1; · funext i; have H (j:ℕ):= Nat.zero_le (height R P j); simp [enamel,drift,relict]; unfold Coefficient.exponentialEntry; unfold F X'; abel
    simp only [Nat.cast_zero,mul_zero,Real.exp_zero]; ring
end YM.OPE.Vitrines

