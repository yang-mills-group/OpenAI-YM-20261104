import YM.FVA2.Slice.Read

/-! # Identification of Wilson, gauge and Haar vertices, at all ranks -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Finset Lattice
open MS MS.Plane MS.Cylinder Lab MS.Cylinder.Taylor MS.Book Convolve MS.Tone MS.City MS.Orbit
open MS.Koszul MS.Landau MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Bare Focus
open Pert Orb Fourier
open Wick (Index bos bar sector eased Inks xy pull_product)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {A J : Type}
local notation "T" => Site n
local notation "L" => Transverse G n
local notation "Z" => SiteGhost G n
local notation "Λ" => ToneS G × T
local notation "Ω" => Mind G T
local notation "D" => Native.Eyes G T
local notation "Π₀" => panel G T
local notation "K" => Native.Paper G T
local notation "Γ" => glow G T
local notation "f" => Chart.loco (drive n) (G:=G)
local notation "p" => Chart.roam (drive n) (G:=G)

private def compR (i : Ω) (z : Z) (v : L) := (Γ).seed i (p (includeA G n v) z.val)
private def linkG (i : Ω) (z : Z) := projector i (gM z).val
private def coord (i : D) (z : Z) := projector i z.val
private lemma compR_calc (i : Ω) (z : Z) : compR i z = ∑ j:D, coord j z • ((Γ).seed i ∘ f j ∘ incCL G n) := by
  funext v; rw [Finset.sum_apply]; unfold compR
  -- expand z.val using ordinary basis priv
  nth_rw 1 [← Native.frame z.val]; rw [map_sum, map_sum]; simp_rw [map_smul]; rfl
private lemma compR_s (i : Ω) (z : Z) : germ (compR i z) := by
  let g := fun a:L=> Chart.roam (drive n) (G:=G) (includeA G n a) z.val
  have h : ContDiffAt ℝ ω ((Γ).seed i) (g 0) := ((Γ).seed i).contDiff.contDiffAt
  exact h.comp 0 (roam_analytic (G:=G) z.val)
private lemma pair_comp (y z : Z) : (fun v:L=> pair v y z) = (1/2:ℝ) • ∑ i:Ω, linkG i y • compR i z := by
  funext v; unfold pair linkPair
  rw [Fintype.sum_prod_type (α₁:=Edge T), Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_inv_mul, one_div]; congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [PiLp.inner_apply, Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _
  rw [Pi.smul_apply]; unfold linkG compR; change inner ℝ _ _ = projector _ _ * projector _ _
  rw [projector_k,projector_k, Real.inner_apply,mul_comm]

namespace Axes
variable (a : Axes G n A J) [Fintype J] [DecidableEq J]
local notation "b" => sector (A:=A) (J:=J)
local notation "I" => Index A J
local notation "X" => Inks (J:=J) a.X
local notation "δ" => Wick.pull a.P
local infixl:70 " ⋆ " => product b
local infixl:70 " ⋆₀ " => product (σbranch (G:=G) (n:=n))
local notation "μ" => (↑((1/2):ℝ):ℂ)

omit [Fintype J] [DecidableEq J] in
lemma mulconst_ink (g : L → ℝ) (c : ℝ) (hg : germ g) : X (c • g) = (c:ℂ) • X g := ink_smul _ hg c
lemma pay_is_half : Cog.pay true = μ := by norm_num [Cog.pay]
lemma Haar_contact : δ (Cog.pay true • docket n (Wilsonian.H G)) = X (haar G n) := by
  rw [Wilsonian.shiftD]; change δ (Cog.pay true • reads Chart.totalH) = _
  rw [map_smul, pay_is_half, a.read_pull (h:=nice_totalH)]
  have he : germ (totalH ∘ incCL G n) := calm (by exact nice_totalH)
  rw [show haar G n=(1/2:ℝ) • (totalH ∘ incCL G n) from funext (fun x=>by
    change _/2 = 1/2 * totalH (includeA G n x); ring), a.mulconst_ink _ _ he]

variable [Fintype A]
private lemma stone_pull (i : Ω) : δ (stone Γ f i) =
    ∑ j:J, atLetter (Wick.ghost j) ⋆ X (compR i (a.c j)) := by
  let k (j : J) := a.c j
  unfold stone
  change δ (∑ j:D, ((Π₀).spark j) ⋆₀ reads ((Γ).seed i ∘ f j)) = ∑ j, atLetter (Wick.ghost j) ⋆ X (compR i (k j))
  have h (j:D) : germ ((Γ).seed i ∘ f j) := ((Γ).seed i).contDiff.contDiffAt.comp 0 (Chart.ride (drive n) j)
  let g (j : D) := (Γ).seed i ∘ f j ∘ incCL G n
  have hv (j : D) : germ (g j) := calm (h j)
  have hh (i:D) : δ ((Π₀).spark i)=∑ j:J,(coord i (a.c j):ℂ) • atLetter (Wick.ghost (A:=A) j) := by
    unfold coord; simp_rw [projector_k]; exact a.spin_ghost i.1 i.2
  rw [map_sum]; simp_rw [pull_product a.tie, a.read_pull (h _), hh, map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,compR_calc i]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  rw [Inks, ink_sum _ _ (fun u _=>show germ (coord u (k j) • g u) from (hv u).const_smul (coord u (k j))), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = _ ⋆ X (coord i (k j) • g i); rw [mulconst_ink a (g i) _ (hv i), map_smul]; rfl

local notation "α" => launch Γ (colorTerm G T) f
private lemma hung_pull : δ (Cog.pay true • (K).hung α) =
    ∑ i:J, ∑ j:J, (Wick.xy i j) ⋆ X (fun v=> a.M v i j) := by
  have off (i:D) : δ (atLetter ((K).dual ((Π₀).KId i)))=0 := a.spin_B i.1 i.2
  have he (i:Ω) : δ (atLetter ((K).dual ((Π₀).AId i))) = ∑ j:J, (linkG i (a.Y j):ℂ) • atLetter (bar (A:=A) j) := by unfold linkG; simp_rw [projector_k]; exact a.spin_anti i.1 i.2
  rw [Bonded.hung,(Π₀).split_i]; simp only [map_smul,map_add,map_sum,pay_is_half]; -- pull_product needs defeq
  have ht y z : δ (product (field Landau.parity) y z) = _ := Wick.pull_product a.tie y z
  simp_rw [ht, off, map_zero, LinearMap.zero_apply,smul_zero, Finset.sum_const_zero, add_zero, he,
    launch_stone,stone_pull a, Native.feeA,one_smul, Finset.smul_sum,map_sum,
    LinearMap.sum_apply, map_smul,LinearMap.smul_apply, Finset.smul_sum]
  conv_lhs =>
    arg 2
    intro x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  -- regroup analytic ink pair
  rw [show (fun v : L=> a.M v i j)=(fun v:L=> pair v (a.Y i) (a.c j)) from rfl,pair_comp]
  let y := a.Y i; let z := a.c j
  have hs k : germ (linkG k y • compR k z) := (compR_s k z).const_smul (linkG k y)
  rw [a.mulconst_ink _ _ (show germ (∑ k:Ω,linkG k y • compR k z) from ?_), Inks,
      ink_sum _ _ (fun k _ => hs k), map_smul, map_sum, Finset.smul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    change μ • ((linkG k y:ℂ) • _) = μ • ((Wick.xy i j) ⋆ X (linkG k y • compR k z))
    rw [a.mulconst_ink _ _ (compR_s k z),map_smul, Wick.xy,times_assoc]
  unfold germ; rw [funext (fun x=> Finset.sum_apply x Finset.univ (fun k => linkG k y • compR k z))]
  exact ContDiffAt.sum fun k _ => hs k

theorem Wilson_contact : δ (Cog.pay true • docket n (Wilsonian.W G)) = -X (Slice.W G n) +
    ∑ i:J, ∑ j:J, Wick.xy i j ⋆ X (fun v => a.M v i j) := by
  rw [Wilsonian.witnessD]; change δ (Cog.pay true • (reads (Chart.rent (drive n)) + (K).hung α)) = _
  rw [smul_add,map_add,hung_pull a,map_smul, pay_is_half, a.read_pull (h:=rent_s (drive n))]
  rw [show Chart.rent (drive n) ∘ incCL G n = (-2 : ℝ) • Slice.W G n from funext W_rent,
      a.mulconst_ink _ _ (W_smooth _ _), smul_smul]; norm_num
end Axes
end YM.FVA2.Slice
