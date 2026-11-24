import YM.GradedFar.Growth.Relay

/-! # Compact counting intervals for the growth iteration. -/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "K"=> Kseries N M

abbrev factor (x y : ℂ) : ℕ→ℂ
| 0=>0
| n+1=> factor x y n*x+y^n
lemma factor_eq (x y : ℂ) (n : ℕ) : (x-y)*factor x y n=x^n-y^n := by
    induction n with
    | zero=> simp [factor]
    | succ n ih=> rw [factor, mul_add, ← mul_assoc, ih, pow_succ, pow_succ]; ring
lemma cont_factor (n : ℕ) : Continuous (fun p:ℂ × ℂ=> factor p.1 p.2 n) := by
    induction n with
    | zero=> exact continuous_const
    | succ n ih=> exact (ih.mul continuous_fst).add (continuous_snd.pow _)
section
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
def chord (v : ℝ → Portion E) (p : ℕ) (z : (ℂ × ℂ)× ℝ) := ∑ i∈Finset.range (p+1), factor z.1.1 z.1.2 i • v z.2 i
lemma tuned_chord (v : ℝ→Portion E) (p : ℕ) (s : ℝ) (x y : ℂ) :
    blend (v s) p x-blend (v s) p y = (x-y) • chord v p ((x,y),s) := by
  unfold blend chord; rw [← Finset.sum_sub_distrib,Finset.smul_sum]; simp_rw [smul_smul,factor_eq,sub_smul]
lemma cont_chord (v : ℝ→Portion E) (h : ∀ j, Continuous (fun i=> v i j)) (p : ℕ) : Continuous (chord v p) :=
    continuous_finsetSum _ (fun i _=>(Continuous.smul ((cont_factor i).comp continuous_fst) ((h i).comp continuous_snd)))
end
abbrev doubling : ℝ := Real.log 2
lemma doubling_pos : 0<doubling := Real.log_pos one_lt_two
abbrev Small : Set ℝ:= Icc 0 doubling
lemma uniform_on_compact (V:(ℂ × ℂ)× ℝ→ℝ)(h:Continuous V)(k:ℝ)
    (ht : ∀ i∈Small, V (0,i)<k) : ∀ᶠ z:ℂ × ℂ in 𝓝 0,∀ i∈Small, V (z,i)<k := by
    obtain ⟨U,W,hU,hW,h0,hq,he⟩:= generalized_tube_lemma isCompact_singleton (show IsCompact Small from isCompact_Icc)
      (show IsOpen (V ⁻¹' Iio k) from isOpen_Iio.preimage h) (show {(0:ℂ × ℂ)} ×ˢ Small ⊆ V ⁻¹' Iio k from by rintro ⟨i,j⟩ ⟨hg,hj⟩; have hg : i=0:=mem_singleton_iff.mp hg; subst i; exact ht j hj)
    exact (show ∀ᶠ z in 𝓝 0,z∈U from hU.mem_nhds (singleton_subset_iff.mp h0)).mono (fun z hz i hi=> he (show (z,i)∈U×ˢ W from ⟨hz,hq hi⟩))

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma bends_price (p : ℕ) (hp : 1≤p) : ∀ᶠ z:ℂ × ℂ in 𝓝 0, ∀ i∈Small,
    ‖bend N M i p z.1-bend N M i p z.2‖ ≤ 2 * ‖z.1-z.2‖ := by
    let c := fun s=> tells (ψ (-s))
    have hc := (cont_chord c (fun i=> continuous_rhythm (psi_rhythm N M H i)) p).norm
    have he s : chord c p (0,s)=1 := by
      unfold chord; rw [Finset.sum_eq_single 1]
      · unfold factor c tells; simp [(tendsK N M H s).lead]
      · intro b hb hx; cases b with
        | zero=> exact zero_smul ..
        | succ b=> rw [factor]; dsimp only [Prod.fst_zero,Prod.snd_zero]; rw [mul_zero,zero_pow (by omega),zero_add,zero_smul]
      intro h; simp at h; omega
    have hv := uniform_on_compact (fun i=> ‖chord c p i‖) hc 2 (fun i hi=> by rw [he,norm_one]; norm_num)
    filter_upwards [hv] with z h i hi; unfold bend; rw [tuned_chord c p i,norm_smul,mul_comm (2:ℝ)]
    exact mul_le_mul_of_nonneg_left (show ‖chord c p _‖ ≤2 from (h i hi).le) (norm_nonneg _)
lemma cranks_price (p d : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ z:ℂ × ℂ in 𝓝 0, ∀ i∈Small,
    ‖crank N M d i p z.1-crank N M d i p z.2‖ ≤ C * ‖z.1-z.2‖ := by
    let c:=fun s=> names (K d (-s))
    have hc:=cont_chord c (fun i=> Kcontinuity N M H i d) p
    obtain ⟨C,h⟩:= isCompact_Icc.exists_bound_of_continuousOn (s:=Small) (f:=fun i=> chord c p (0,i))
      (hc.comp (continuous_const.prodMk continuous_id)).continuousOn
    refine ⟨max 1 (C+1),le_max_left ..,?_⟩
    have hv:= uniform_on_compact _ hc.norm (C+1) (fun i hi=> lt_of_le_of_lt (h i hi) (lt_add_one _))
    filter_upwards [hv] with z h i hi; unfold crank; rw [tuned_chord c p i,norm_smul,mul_comm (max ..)]
    exact mul_le_mul_of_nonneg_left (le_trans (h i hi).le (le_max_right ..)) (norm_nonneg _)
end
end YM.FVA2.GradedFar.Growth
