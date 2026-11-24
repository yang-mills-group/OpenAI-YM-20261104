import YM.Integration.WilsonReportForwardTransfer

/-! The exact absence of unflagged cross terms on the measured separated stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportDisjointBack
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker
open Push Push.GridApprox OPE OPE.Strobe OPE.Yarn OPE.Strobe.Vista26
open Extra.Multi Next.Rank Next.Rank.Spindle PhysicalNext.Repeat.Legato MergeProof.Ribbons.ManyCopies.Patrol
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V] {W r D}

private theorem cover (hG : G.Simple) (a : ℕ) :
    ∀ᶠ k : ℕ in atTop, a≤(C.path.levels.budget k).B := by
  have hi := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate C.path.levels hG)
  filter_upwards [hi.eventually_ge_atTop ((a:ℝ)+1)] with k high
  let b := Real.log (C.path.levels.clock.hatBeta k)
  apply (Nat.cast_le (α:=ℝ)).mp
  have hg : (a:ℝ)+1≤b := high
  have ht : b^2≤((C.path.levels.budget k).B:ℝ) := Nat.le_ceil _
  nlinarith only [hg,ht,Nat.cast_nonneg (α:=ℝ) a]

/-- The original finite column support, including the full kernel halo, lies
strictly below half the native minimal separation at every late stage. -/
theorem separation (hG : G.Simple) (citizen : Citizen C W r D) (d : ℕ) :
    ∀ᶠ i : ℕ in atTop, 2*muzzle C.path.levels i (omen C d i (C.path.levels.budget i).B) <
      (C.path.levels.budget i).B^8 := by
  have grow := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate C.path.levels hG)
  filter_upwards [grow.eventually_ge_atTop 1,cover (C:=C) hG (BasisCost.extent (C.localSection d)),cover (C:=C) hG 100] with i hz ht hs
  let k := (C.path.levels.budget i).B
  let x := C.path.levels.clock.J i
  have h : x≤k := by
    apply (Nat.cast_le (α:=ℝ)).mp
    let z := Real.log (C.path.levels.clock.hatBeta i)
    have hp : 1≤z := hz
    have hx : 100000*((x:ℝ)+1)≤z := (citizen.safeguards.stage i).pedestal
    have hf : z^2≤(k:ℝ) := Nat.le_ceil _
    nlinarith only [hp,hx,Nat.cast_nonneg (α:=ℝ) x,hf]
  let b := BasisCost.extent (C.localSection d)
  change 2*(b+(k*(4*k+2)+2*k+8)+30*(x+5))<k^8
  change b≤k at ht
  change 100≤k at hs
  have hα : k^3≤k^8 := pow_le_pow_right₀ (by omega) (by decide : 3≤8)
  nlinarith only [mul_le_mul_of_nonneg_right hs (Nat.zero_le (k^2)),ht,hs,hα,h]

/-- Exact factorization at every actual microscopic configuration, for the all-bead
branch only. No common upper bound on the distances between the sites is needed. -/
theorem entire (hG : G.Simple) (hC : C.Makes) (citizen : Citizen C W r D) (d : V→ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, ∀ hk : k≤N, ∀ x : V→Site (C.side k p),
    (∀ a b,a≠b → (C.path.levels.budget k).B^8 ≤ Lattice.separation (x a) (x b)) →
    ∀ v : (j:V)→C.label (d j), ∀ s : Finset V,
    backTo C.path N p hk (fineJob (ScenePack (N:=N) d x v) s) =
      fineJob (fun j => backTo C.path N p hk (ScenePack (N:=N) d x v j)) s := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  filter_upwards [eventually_all.mpr (fun j : V => separation hG citizen (d j)),
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k size refs N p hk x apart v s
  cases isEmpty_or_nonempty V with
  | inl empty =>
    haveI := empty
    have seq : s=∅ := by ext j; exact isEmptyElim j
    rw [seq]
    change backTo C.path N p hk (fun _ => (1:ℂ)) = fun _ => 1
    exact backTo_const C.path N p hk _
  | inr inhabited =>
    haveI := inhabited
    obtain ⟨j,_,largest⟩ := Finset.exists_max_image univ (fun a : V => omen C (d a) k (C.path.levels.budget k).B) univ_nonempty
    let u := omen C (d j) k (C.path.levels.budget k).B
    have inside (i : V) : Cells.Interior (window (x i) u) (ScenePack (N:=N) d x v i) :=
      (bead_local H (x i) (v i) (refs i) hk (C.path.levels.budget k).B).enlarges (by
        intro y hy
        exact sparrow.mpr ((sparrow.mp hy).trans (largest i (mem_univ _))))
    exact backs_many C.path u N p k N x s inside (fun a b h => (size j).trans_le (apart a b h)) hk

end YM.Integration.WilsonReportDisjointBack
end

