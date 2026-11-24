import YM.FormalBulk08.Kemp.Crest
import YM.FormalBulk08.Dawn.Hill

/-! One pointwise transfer from fields profiles. Earth rooted at zero,
mark moves as τ law. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B C : ℝ} {l i u j t r D d : ℕ}

/- Real pointwise input (later receipts ensure linear on p). Use actual offset
 independent profile as in kbulk. -/
abbrev Anthem (D:ℕ)(G: Gauge) := Dawn.Studio D → Pot G
variable (a:Loc G 1)
def Wade (x: Loc G 1)(Y:Anthem D G)(l:ℕ): Prop:=
   (∀ p, Young (Y p) l) ∧ (∀ p e r,Agate (Y p e r)) ∧ ∀ e r,∃ η A: ℝ,0<η ∧ 0≤A ∧ ∀ p, Knoxville (fame _) η (0,x) (Y p e r) (A*‖p‖)
-- topology for EACH profile (we will propagate uniform). Raw formal laws at birth coordinate rank ≤h.
variable {K : KernelChoices}(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(Y:Anthem D G)(ρ : ChartRatio G)(h:P.patch.Branches K G)
-- P requires legal stages imply ≥3 or 1? inspect

def stepsong (hL : 2≤P.L.val)(p: Dawn.Studio D)(x:Site P.L): Pot G:= work (lift x) (Y (Dawn.throughW x _ hL p))
lemma step_can (hz:Wade a Y l)(hL:2≤P.L.val)(p:Dawn.Studio D)(x: Site P.L):Young (stepsong P Y hL p x) l:= by
    intro e r he; apply hz.1; intro hv; unfold stepsong work at he; rw [hv] at he; exact he rfl
lemma step_agate (hz:Wade a Y l)(hL:2≤P.L.val)(p:Dawn.Studio D)(x:Site P.L)(e r : ℕ) : Agate (stepsong P Y hL p x e r):= fun u v=> carrying _ v (hz.2.1 _ _ _) u
lemma step_bill (hz:Wade a Y l)(hL:2≤P.L.val)(e r) : ∃ η A:ℝ,0<η ∧ 0≤A ∧ ∀ p,∀ x:Site P.L, Knoxville (fame _) η (lift x,a) (stepsong P Y hL p x e r) (A*‖p‖):= by
    obtain ⟨s,C,hs,hC,H⟩:=hz.2.2 e r; refine ⟨s,C,hs,hC,fun p x=> ?_⟩; have ht:= mantle_pay (lift x) (H (Dawn.throughW x D hL p) |>.mono (mul_le_mul_of_nonneg_left (Dawn.through_le ..) hC)); rw [show Lotus.tint (lift x) (show edgeL G from (0,a))=(lift x,a) from Prod.ext (zero_add _) rfl] at ht; exact ht
-- Output anchored STEP union

def aven (L:Side)(d:ℕ):ℝ:= (L.val:ℝ)^d * (Fintype.card (Site L):ℝ)⁻¹
lemma aven_pos (L:Side)(d:ℕ):0<aven L d:=by unfold aven; positivity

def quick (hL: 2≤P.L.val)(d u:ℕ) : Anthem D G:= fun p=> aven P.L d • ∑ x:Site P.L, braise P V W (stepsong P Y hL p x) ρ h u
lemma quick_yield (hL:2≤P.L.val)(hy:Wade a Y l)(hw:Vivid W)(hv: LocalRatio ρ)(p:Dawn.Studio D): Young (quick P V W Y ρ h hL d u p) l:= by
    intro e r he; unfold quick at he; by_contra H; simp only [Pi.smul_apply,Finset.sum_apply] at he; rw [Finset.sum_eq_zero (f:=fun x=>braise P V W _ ρ h u e r) (fun x _=> ?_), smul_zero] at he;contradiction
    by_contra hb; exact H (truss (K:=K) _ _ _ _ ρ _ hw hv (step_can a P Y hy hL p x) _ e r hb)

def quickP (hL:2≤P.L.val)(d u:ℕ)(p:Dawn.Studio D)(n:Side)(k: (primary P.patch K n).Choices) := PowerSeries.C (MvPolynomial.C (aven P.L d)) * ∑ x:Site P.L,tossed P ρ h V n k (stone W _) (banner u (stepsong P Y hL p x) _)
lemma quick_income (hL:2≤P.L.val)(p:Dawn.Studio D)(n:Side)(k: (primary P.patch K n).Choices)(e r:ℕ):
   rancho (quickP P V W Y ρ h hL d u p n k) e r= aven P.L d • ∑ x:Site P.L, rancho (tossed P ρ h V n k (stone W _) (banner u (stepsong P Y hL p x) _)) e r := by
   unfold quickP rancho; simp_rw [←canyon_eq,coeff_C_mul,map_sum,show ∀ a:ℝ,∀ g:TypeR (wire G n),MvPolynomial.C a*g=a • g from fun a g=> by rw [MvPolynomial.smul_eq_C_mul]]; rw [map_smul,map_sum]
lemma quickP_breeze (hL:2≤P.L.val)(hy:Wade a Y l)(hw:Story W (pink K.penalty P.wing))(hv:LocalRatio ρ)(he:l≤u)(hs:4≤t)(p:Dawn.Studio D)(n:Side)(k:(primary P.patch K n).Choices): Young (rancho (quickP P V W Y ρ h hL d u p n k)) l := by
   intro e r H; by_contra hp;rw [quick_income] at H; refine H ?_; rw [Finset.sum_eq_zero, smul_zero]; intro x _; by_contra hx; exact hp ((tossed_gen _ _ _ _ ρ _ hw hv hs (step_can a P Y hy hL p x) u (step_agate a P Y hy hL p x) he n k e r hx))
end YM.FormalBulk08.Kemp
