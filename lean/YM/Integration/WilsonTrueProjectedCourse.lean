import YM.Integration.WilsonTrueProjectedColumnDescent
import YM.Extra.WILSON_STARTUP.Fast

/-! The actual Wilson gate is elected before either regulator. The sum of
all earlier signed forcing bills has the same fixed power of the charged
clock as the one-date invoice. The true upper boundary and its physical
mesh gain are retained separately. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedCourse
open Filter MeasureTheory Lattice Wilson RG Source Labels
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay Bid MergeProof WilsonTrueProjectedColumnDescent
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G)
local notation "𝓡" => R.family

def power (q : ℕ) (j : ℕ) : ℝ :=
  (max 1 ((𝓡).path.levels.clock.hatBeta j)) ^ (-(q:ℝ)/2)

private theorem monotone_price (simple : G.Simple) (q : ℕ) : Antitone (power R q) := by
  intro i j ij
  have increasing := WilsonStartup.Timing.hat_mono (𝓡).path.levels (Gauge.slopeConstant_pos simple).le ij
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (max_le_max_left 1 increasing) (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num))

theorem mesh_gain (C : Family G) (n i : ℕ) :
    retained C n i = Real.exp (-GermGraph.rate * (C.S.scale (i+n)-C.S.scale i)) := by
  induction n generalizing i with
  | zero => simp [retained]
  | succ n ih =>
    have h : (0:ℝ) < factor C i := zero_lt_one.trans (factor_positive C i)
    rw [retained,ih,decay,Real.rpow_def_of_pos h,←Real.exp_add,Schedule.scale_succ]
    rw [show i+1+n = i+(n+1) by omega]
    congr 1
    change Real.log ((C.S.block i).val:ℝ)*(-GermGraph.rate) + _ = _
    ring

theorem original (simple : G.Simple) (d q : ℕ) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ b N p : ℕ, k ≤ b → b ≤ N →
    ∀ (col e : ∀ j, store (𝓡) d p j) (v : ℕ → (𝓡).label d) (price : ℕ → ℝ)
      (M boundary : ℝ), 0 ≤ M →
    (∀ j ≥ k, j ≤ b → measuring (𝓡) d N p j (v j) = page (C:=𝓡) d p j (col j)) →
    (∀ j ≥ k, j < b → ∃ t, reads d N p j (col j) t) →
    (∀ j ≥ k, j < b → reads d N p j (e j) (price j) ∧
      ((𝓡).labels.level d).coeffSize (e j).x ≤ price j ∧
      (1+4*stock (𝓡) j)*price j ≤
        (1-(3:ℝ)^(-GermGraph.rate))*(M*power R q j)) →
    (∀ j ≥ k, j < b → transition (C:=𝓡) d N p j (value d N p (j+1) (col (j+1))) =
      value d N p j (col j) + value d N p j (e j)) →
    (∃ s : store (𝓡) d p b, reads d N p b s boundary ∧ page (C:=𝓡) d p b s=0 ∧
      value d N p b s = calValues d N p b (v b) - value d N p b (col b)) →
    ∃ s : store (𝓡) d p k, reads d N p k s
      (Real.exp (-GermGraph.rate*((𝓡).S.scale b-(𝓡).S.scale k))*boundary + M*power R q k) ∧
      page (C:=𝓡) d p k s=0 ∧ value d N p k s = calValues d N p k (v k) - value d N p k (col k) := by
  filter_upwards [ActualOneMarkGraphStep.gates R simple d hγ hε] with k gates
  intro b N p kb bN col e v price M boundary hM amounts admitted bills matchStep init
  let opened := fun j (jk : k ≤ j) (jb : j < b) => (gates j jk p N (jb.trans_le bN)).1.1
  let gate := fun j (jk : k ≤ j) (jb : j < b) => (gates j jk p N (jb.trans_le bN)).2
  obtain ⟨s,hs,zero,represented⟩ := history R.makes bN col e v price opened gate amounts admitted
    (fun j jk jb => (bills j jk jb).1) matchStep init k le_rfl kb
  have threshold (j : ℕ) : decay (𝓡) j ≤ (3:ℝ)^(-GermGraph.rate) := by
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast (𝓡).S.block_large j)
      (by norm_num [GermGraph.rate])
  have positive (j : ℕ) : 0 ≤ M * power R q j :=
    mul_nonneg hM (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have mono := monotone_price R simple q
  have rated (j : ℕ) (jk : k ≤ j) (jb : j < b) :
      invoice e price j ≤ (1-(3:ℝ)^(-GermGraph.rate))*(M*power R q j) := by
    obtain ⟨he,hx,hb⟩ := bills j jk jb
    have hstock : 0 ≤ 2*stock (𝓡) j :=
      mul_nonneg zero_le_two (zero_le_one.trans (stage (𝓡) j).columns_ge)
    have hpage : ((𝓡).labels.level d).coeffSize (page (C:=𝓡) d p j (e j)) ≤ 2*price j :=
      control_page R.makes (opened j jk jb) (jb.le.trans bN) (e j) he hx
    apply le_trans _ hb
    calc
      invoice e price j ≤ price j + (2*stock (𝓡) j)*(2*price j) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hpage hstock)
      _ = _ := by ring
  have estimate := bounded (𝓡) (fee:=invoice e price) (cap:=fun j => M*power R q j)
    boundary ((3:ℝ)^(-GermGraph.rate)) k b (fun j _ _ => positive j)
    (fun j _ _ => mul_le_mul_of_nonneg_left (mono (Nat.le_succ j)) hM)
    (fun j _ _ => threshold j) rated k le_rfl (b-k) (by omega)
  rw [mesh_gain,show k+(b-k)=b by omega] at estimate
  exact ⟨s,⟨hs.1,rem_increase d hs.2 estimate⟩,zero,represented⟩

end YM.Integration.WilsonTrueProjectedCourse
