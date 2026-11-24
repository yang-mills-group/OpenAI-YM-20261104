import YM.Integration.WilsonReportDisjointBack
import YM.Integration.WilsonReportSeparatedMoments

/-! Arbitrarily scheduled mixed original fine and coarse marks on a single separated report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportPartialShell
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol Push.GridApprox
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] {W r D} {k N p : ℕ}

/-- Only the independently scheduled slots in M are replaced. All other
original columns are literal fine, spatial Wilson fields at their anchored sites. -/
def hybrid (M : Finset V) (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p))
    (v : (j:V)→C.label (d j)) (j : V) : Config G (C.side N p)→ℂ :=
  if j∈M then backTo C.path N p hk (ScenePack (N:=N) d x v j) else BarePack d x hk v j

private theorem covers (n t q : ℕ) {b : ℝ} (hb : 3≤b) (hn : (n:ℝ)≤b) {j : ℕ} (hj : j≤n) :
    (j:ℝ)*(b^(q+(t+1)*n+1))⁻¹*(2+b^t)^j≤(b^q)⁻¹ := by
  have b1 : 1≤b := by linarith
  have bp : 0<b := zero_lt_one.trans_le b1
  have worth := one_le_pow₀ b1 (n:=t)
  have base : 2+b^t≤b^(t+1) := calc
    _ ≤ 3*b^t := by linarith
    _ ≤ b*(b^t) := mul_le_mul_of_nonneg_right hb (pow_nonneg bp.le _)
    _ = _ := by ring
  have pwr := (pow_le_pow_left₀ (by positivity : 0≤2+b^t) base j).trans (pow_le_pow_right₀ (one_le_pow₀ b1) hj)
  calc
    _ ≤ b*(b^(q+(t+1)*n+1))⁻¹*(b^(t+1))^n := mul_le_mul
      (mul_le_mul_of_nonneg_right ((by exact_mod_cast hj : (j:ℝ)≤n).trans hn) (by positivity)) pwr (by positivity) (by positivity)
    _ = _ := by rw [←pow_mul,pow_succ,pow_add]; field_simp

/-- True subset moments with any chosen collection of fine spectator marks
left untouched. On compact separated profiles the early flagged sectors cost
every inverse power, uniformly in this independent schedule, before cutoff and period. -/
theorem moments [Fintype V] (hG : G.Simple) (hC : C.Makes) (citizen : Citizen C W r D)
    (d : V→ℕ) {br : ℕ} (hbr : 0<br) (t q : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ dis : ℕ,(C.path.levels.budget k).B^8≤dis →
    (dis:ℝ)≤C.path.levels.clock.hatBeta k → ∀ N p, ∀ hk : k<N, ∀ x : V→Site (C.side k p),
    Sites26 (C:=C) br dis x → ∀ v : (j:V)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ M s : Finset V,
    ‖moment (C.beta N p) (fineJob (BarePack d x hk.le v) s)-
      moment (C.beta N p) (fineJob (hybrid M hk.le d x v) s)‖ ≤ (C.path.levels.clock.hatBeta k^q)⁻¹ := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  let n := Fintype.card V
  let z := q+(t+1)*n+1
  have Hs (u : Finset V) := uniformShell (J:=(↑u : Type)) H citizen hbr (fun j => d j.val) 1 t z
  have grow := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [eventually_all.mpr Hs,grow.eventually_ge_atTop 3,grow.eventually_ge_atTop (n:ℝ),
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k pay large arity refs
  intro dis low high N p hk x geom v funds M s
  let μ := law G (C.side N p) (C.beta N p)
  let b := C.path.levels.clock.hatBeta k
  let A := BarePack d x hk.le v
  let B := hybrid M hk.le d x v
  let c := fun j => cameo C (d j) k N p (v j)
  let Wt := fun (f : V→Bool) j => writeF C (v j) N k p (C.path.levels.budget k).B (x j) hk.le (f j)
  have b1 : 1≤b := (C.path.levels.fits.delayed k).le
  have eA (j) : Envelope (A j) := Envelope.compactC (C.continuousO ..)
  have eB (j) : Envelope (B j) := by
    by_cases marked : j∈M
    · simpa only [B,hybrid,marked,if_true] using backTo_env C.path N p hk.le
        (cylinder_env (Strobe.bead_local H (x j) (v j) (refs j) hk.le (C.path.levels.budget k).B))
    · simpa only [B,hybrid,marked,if_false] using eA j
  have flagged (u : Finset V) (f : V→Bool) (onMark : ∃ j∈u,f j=true) :
      ‖∫ Z,Moment.pick (fun j => Moment.write A B c j (f j)) u Z ∂μ‖≤(b^z)⁻¹ := by
    by_cases off : ∃ j∈u,j∉M ∧ f j=true
    · obtain ⟨j,ju,no,yes⟩ := off
      have zero (Z) : Moment.pick (fun i => Moment.write A B c i (f i)) u Z=0 := by
        apply Finset.prod_eq_zero ju
        change (if f j then A j-B j else fun Z => A j Z-c j) Z=0
        simp [yes,A,B,hybrid,no]
      simp only [zero,integral_zero,norm_zero]
      positivity
    have field (j) (ju : j∈u) : Moment.write A B c j (f j)=Wt f j := by
      have actual := (erased (k:=k) (v j) (C.path.levels.budget k).B (x j) hk.le (f j)).symm
      change (if f j then A j-B j else fun Z => A j Z-c j) =
        writeF C (v j) N k p (C.path.levels.budget k).B (x j) hk.le (f j)
      by_cases marked : j∈M
      · have inM : B j=backTo C.path N p hk.le (ScenePack (N:=N) d x v j) := by simp [B,hybrid,marked]
        rw [inM]
        exact actual
      · have hfalse : f j=false := by cases hj : f j with
                                       | false => rfl
                                       | true => exact (off ⟨j,ju,marked,hj⟩).elim
        rw [hfalse] at actual ⊢
        exact actual
    let xu := fun j : (↑u : Type) => x j.val
    have geometry : Sites26 (C:=C) br dis xu := ⟨fun a b => geom.close ..,
      fun a b ne => geom.apart _ _ (fun e => ne (Subtype.ext e))⟩
    have yes : ∃ j : (↑u : Type),f j.val=true := by
      obtain ⟨j,ju,hj⟩ := onMark
      exact ⟨⟨j,ju⟩,hj⟩
    have leaf := pay u dis low (by simpa only [pow_one] using high) N p hk xu geometry
      (fun j => v j.val) (fun j => funds j.val) (fun j => f j.val) yes
    have eq : Moment.pick (fun j => Moment.write A B c j (f j)) u =
      fineJob (fun j : (↑u : Type) => Wt f j.val) univ := by
      funext Z
      change (∏ j∈u, Moment.write A B c j (f j) Z) = _
      rw [Finset.prod_congr rfl (g:=fun j => Wt f j Z) (fun j hj => congr_fun (field j hj) Z)]
      exact Finset.prod_subtype u (fun _ => Iff.rfl) _
    rw [eq]
    exact leaf
  have replaced := Moment.replacement μ A B c eA eB (pow_nonneg (zero_le_one.trans b1) t)
    (fun j => Strobe.cameo_price (v j) (funds j)) (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans b1) z)) flagged s
  exact replaced.trans (covers n t q large arity (card_le_univ s))

end YM.Integration.WilsonReportPartialShell
end

