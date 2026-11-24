import YM.Integration.WilsonMacroscopicRichProbeShell

/-! Nonlinear cropped read of the complete signed rooted series before any cutoff limit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCroppedSeries
open Function Filter Lattice Wilson RG Source Analysis Labels Next.Foundations ProjectorNext.Equivariance
open WilsonMacroscopicRichCroppedProbe
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open private ray_sum from YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Line
variable {G:Gauge} {n:Side} {P:BudgetPoint}

theorem submitted {ι : Type*} {D : ι → Support n} {g : ι → Config G n → ℂ} {c : ι → ℝ} {o : Site n}
    (h : ∀ i, P.Regular (D i) (g i)) (hc : ∀ i, P.supBounds o (D i) (g i) (c i)) (hh : Summable c)
    {f : Config G n → ℂ} (hf : f =ᶠ[𝓝 (1:Config G n)] fun U => ∑' i, g i U)
    (d : ℕ) (he : HasOrderAt f 1 d) (hd : d ≤ P.order) (A : Hol G) (J : Jet G) (k : ℕ) (hk : k≤d) (Aset : Finset (Edge (Site n))) :
    HasSum (fun i => iteratedDeriv k (fun t => g i (fields Aset A d o J t)) 0) (iteratedDeriv k (f ∘ fields Aset A d o J) 0) := by
  have hp (i : ι) : HasOrderAt (g i) 1 d := HasOrderAt.fewer hd
    ((h i).smooth _ (one_healthy (D i) _ P.threshold_pos.le))
  let K (F : Config G n → ℂ) j := iteratedFDeriv ℝ j (F ∘ increment 1) 0
  have hu (j : ℕ) (hJ : j ≤ d) (x) : HasSum (fun i => K (g i) j x) (K f j x) := by
    refine polarization_sum (sym_Jet (he.fewer hJ)) (fun i => sym_Jet ((hp i).fewer hJ)) ?_ x
    intro A
    have hw (u : Config G n → ℂ) (ht : HasOrderAt u 1 d) : Tensor.diagonal (K u j) A =
        iteratedDeriv j (fun t : ℝ => u (increment 1 (t • A))) 0 := (iteratedDeriv_on_line (ht.fewer hJ) A).symm
    change HasSum (fun i => Tensor.diagonal (K (g i) j) A) (Tensor.diagonal (K f j) A)
    rw [hw f he]; simp_rw [hw (g _) (hp _)]
    exact ray_sum h hc hh hf A _ (hJ.trans hd)
  let B := mask Aset ∘ testLog A d o J
  let v (a : OrderedFinpartition k) (i : Fin a.length) := iteratedDeriv (a.partSize i) B 0
  have hx (u : Config G n → ℂ) (ht : HasOrderAt u 1 d) : iteratedDeriv k (u ∘ fields Aset A d o J) 0 =
      ∑ a : OrderedFinpartition k, K u a.length (v a) := by
    have hl : B 0=0 := by dsimp [B];rw [testLog_zero,map_zero]
    change iteratedDeriv k ((u ∘ increment 1) ∘ B) 0 = _
    rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition
      (show ContDiffAt ℝ d (u ∘ increment 1) (B 0) by rw [hl]; exact ht)
      (((mask (G:=G) Aset).contDiff.contDiffAt.comp 0 (testLog_diff A d o J)).of_le le_top) (Nat.cast_le.mpr hk),hl]
  rw [hx f he]; change HasSum (fun i => iteratedDeriv k (g i ∘ _) 0) _
  simp_rw [hx (g _) (hp _)]
  exact hasSum_sum fun i _ => hu _ (i.length_le.trans hk) _
end YM.Integration.WilsonMacroscopicRichCroppedSeries
