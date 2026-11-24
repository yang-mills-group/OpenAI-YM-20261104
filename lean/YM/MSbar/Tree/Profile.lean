import YM.MSbar.Tree.JetCov

/-!
# Tree comparison queries

Type of moving regulators for the leading perturbative estimates. Use inverse
spacing `r` increasing; placements integer sites measured relative to an
origin. We prove along EVERYTHING in this regime (`Juxtaposed`), using
compact separated shape costs. Theorems take an arbitrary filter (so usable
also for uniform families, not after choosing centers). All estimates in
these units pointwise, before any position tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree
open Function Set Filter Lattice Analysis Asymptotics
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
open Next.Rank Next.Rank.Radian Next.Rank.CellsInt Next.Rank.Beamer Torus

variable {G : Gauge} {k l n : ℕ} {u v : Cover}

/-- Raw regulator data. Require even side and only use it in its supported regime. -/
structure Query (n : ℕ) where
  r : ℝ
  positive : 0 < r
  nsites : Side
  even : Even nsites.val
  origin : Cover
  points : Fin n → Cover

namespace Query
def shape (x : Query n) : Points n := YM.points fun i=> x.r⁻¹ • mapZ (x.points i-x.origin)
lemma offsets (x : Query n) (i j : Fin n) : x.shape i-x.shape j=x.r⁻¹ • mapZ (x.points i - x.points j) := by
  change _ • _ - _ • _ = _
  rw [← smul_sub,← Wall.sends_sub]; simp
end Query

variable {ι : Type*} (Q : ι → Query n) (L : Filter ι)

/-- Require compact separated configurations, but the points can be anywhere
in them, with total lattice alignment and large-volume regime as above. -/
structure Juxtaposed (Q : ι → Query n) (L : Filter ι) : Prop where
  distinct x : (Q x).shape∈ conf n
  holds : ∃ K : Set (Points n), IsCompact K ∧ K ⊆ conf n ∧ ∀ᶠ x in L,(Q x).shape∈K
  placement i : ∀ᶠ x in L, central (Q x).nsites ((Q x).points i)
  rising : Tendsto (fun x=> (Q x).r) L atTop
  growing (d : ℕ) : ∀ᶠ x in L, (Q x).r^d ≤ ((Q x).nsites.val:ℝ)

variable (h : Juxtaposed Q L)
include h
set_option quotPrecheck false
local notation "R" => fun t => (Q t).r
local notation "S" => fun t => (Q t).nsites

lemma grows_nat : Tendsto (fun t => ((S) t).val) L atTop:= by
  apply tendsto_atTop.2; intro i; filter_upwards [h.rising.eventually_ge_atTop (i:ℝ), h.growing 1] with x hr hs
  exact_mod_cast (show (i:ℝ) ≤ (Q x).nsites.val from le_trans hr (by simpa using hs))

private lemma separates (i j : Fin n) (he:i≠j) :
    ∃ A:ℝ, 1≤ A ∧ ∀ᶠ x in L, let z:=mapZ ((Q x).points i-(Q x).points j); (R) x/A ≤ ‖z‖ ∧ ‖z‖ ≤ A*(R) x := by
  obtain ⟨K,hK,hS,hQ⟩:= h.holds
  let f (x: Points n):=‖x i-x j‖; have hf : Continuous f:=by unfold f; fun_prop
  have he x (hx:x∈K) : 0<f x:= norm_pos_iff.mpr (sub_ne_zero.mpr ((show Injective x.ofLp from hS hx).ne he))
  obtain ⟨A,hA,H⟩:= ranges K f hf hK he
  refine ⟨A,hA,?_⟩; filter_upwards [hQ] with x hx
  intro z; let X:= Q x; have hr:= X.positive
  have h₀: f X.shape= ‖z‖/ X.r:= by unfold f; rw [X.offsets,norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]; exact (div_eq_inv_mul ..).symm
  obtain ⟨ha,hb⟩ := H _ hx; change A⁻¹ ≤ f X.shape at ha; change f X.shape ≤ A at hb; rw [h₀, le_div_iff₀ hr] at ha; rw [h₀,div_le_iff₀ hr] at hb; exact ⟨(div_eq_inv_mul ..|>.trans_le ha),hb⟩
where ranges (K : Set (Points n)) (f : Points n → ℝ) (hf : Continuous f) (hK : IsCompact K) (hh : ∀ x∈K,0<f x) : ∃ b : ℝ, 1 ≤ b ∧ ∀ i∈K,f i ∈ Icc b⁻¹ b:= by
        obtain he|he := K.eq_empty_or_nonempty; · simp [he]; exact ⟨1,le_refl _⟩
        obtain ⟨x,hx,H⟩:= hK.exists_isMinOn he hf.continuousOn
        obtain ⟨y,hy,I⟩:= hK.exists_isMaxOn he hf.continuousOn
        let w:=max (max 1 (f y)) (f x)⁻¹; have hw:1 ≤ w:= (le_max_left ..).trans (le_max_left ..);refine ⟨w,hw,fun i hi=> ⟨le_trans ?_ (H hi), (I hi).trans ((le_max_right 1 (f y)).trans (le_max_left ..))⟩⟩
        calc
         _ ≤ ((f x)⁻¹)⁻¹:=inv_anti₀ (inv_pos.mpr (hh x hx)) (le_max_right ..)
         _ = f x:= inv_inv _

lemma image_small (a : Component G k) (b : Component G l) (i j : Fin n) :
    (fun t=> (R) t ^(k+l+4)*imageLine ((S) t) ((Q t).points i) ((Q t).points j) a b) =O[L] (fun t => ((R) t)⁻¹):= by
  obtain ⟨C,hC,hP⟩:= discounted a b; refine IsBigO.of_bound C ?_
  filter_upwards [h.placement i,h.placement j,(grows_nat Q L h).eventually hP,h.growing (k+l+5)] with x hu hv hm hw; let r:= (R) x; let m:=(S) x; have hr:= (Q x).positive; have he:=hm _ le_rfl _ _ hu hv
  rw [norm_mul, Real.norm_of_nonneg (pow_pos hr _).le, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  refine (mul_le_mul_of_nonneg_left he (pow_pos hr _).le).trans ?_
  change r^_*_≤ _; rw [div_eq_mul_inv, mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hC; rw [← div_eq_mul_inv,inv_eq_one_div, div_le_div_iff₀ (Bloch.side_pos m) hr,one_mul,← pow_succ]; exact hw

lemma regular_part (a : Component G k) (b : Component G l) (i j : Fin n) (he:i≠j) :
    (fun t=> (R) t ^(k+l+4)*straight ((S) t) ((Q t).points i) ((Q t).points j) a b - Prayer.gleam (native a) (native b) ((Q t).shape i-(Q t).shape j)) =O[L] (fun t => ((R) t)⁻¹):= by
  obtain ⟨T,hT,H⟩:= separates Q L h i j he; obtain ⟨C,hC,hA⟩:= normalized_bound a b hT
  refine IsBigO.of_bound C ?_; filter_upwards [h.rising.eventually_ge_atTop T, H,h.growing (k+l+6)] with t ht ⟨ha,hb⟩ hw; rw [(Q t).offsets, norm_inv,Real.norm_of_nonneg (Q t).positive.le,←div_eq_mul_inv]; exact hA _ ht _ hw _ _ ha hb

lemma perturb_line (μ : ℝ) (a : Component G k) (b : Component G l) (i j : Fin n) (he:i≠j) :
    (fun t=> (atCut ((R) t) ((S) t) ((Q t).points i) ((Q t).points j) a b:ℂ)- line μ 0 a b ((Q t).shape i-(Q t).shape j)) =O[L] (fun t => ((R) t)⁻¹):= by
  simp_rw [show ∀ t, line μ 0 a b ((Q t).shape i-(Q t).shape j) = _ from fun t=> line_zero _ _ _ _ ( sub_ne_zero.mpr ((show Injective ((Q t).shape.ofLp) from h.distinct t).ne he))] -- t function
  suffices hf : (fun t => ↑(atCut ((R) t) ((S) t) ((Q t).points i) ((Q t).points j) a b-Prayer.gleam (native a) (native b) ((Q t).shape i-(Q t).shape j)):ι→ℂ)=O[L] (fun t=> ((R) t)⁻¹) by simpa using hf
  unfold atCut; simp_rw [mul_add,add_sub_right_comm]
  obtain ⟨C,hC⟩:= ((regular_part Q L h a b i j he).add (image_small Q L h a b i j)).bound; apply IsBigO.of_bound C; filter_upwards [hC] with x hx; rw [Complex.norm_real]; exact hx
end YM.MSbar.Tree
