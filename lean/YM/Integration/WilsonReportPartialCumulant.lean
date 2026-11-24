import YM.Integration.WilsonReportPartialShell
import YM.Integration.WilsonReportForwardTransfer

/-! The independently scheduled connected fine and coarse report from the same Wilson regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportPartialCumulant
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol Push.GridApprox
open WilsonReportMomentDifference WilsonReportPartialShell
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] {W r D} {k N p : ℕ}

/-- Keep the untouched fine observables and sample all scheduled members of each
moment block in a common coarse gauge configuration. -/
def scheduled (Γ : Census V) (M : Finset V) (hk : k≤N) (d : V→ℕ) (x : V→Site (C.side k p))
    (v : (j:V)→C.label (d j)) : Poly Γ := Poly.inject fun s => moment (C.beta N p) fun Z =>
  fineJob (BarePack d x hk v) (s.val\M) Z * backTo C.path N p hk (fineJob (ScenePack (N:=N) d x v) (s.val∩M)) Z

private theorem schedule_eq [Fintype V] (Γ : Census V) (M : Finset V) (hk : k≤N) (d : V→ℕ)
    (x : V→Site (C.side k p)) (v : (j:V)→C.label (d j))
    (back : ∀ s : Finset V,backTo C.path N p hk (fineJob (ScenePack (N:=N) d x v) s) =
      fineJob (fun j => backTo C.path N p hk (ScenePack (N:=N) d x v j)) s) :
    microscopic Γ C (hybrid M hk d x v)=scheduled Γ M hk d x v := by
  ext s
  let A := BarePack d x hk v
  let P := fun j => backTo C.path N p hk (ScenePack (N:=N) d x v j)
  let B := hybrid M hk d x v
  change moment (C.beta N p) (fineJob B s.val)=
    moment (C.beta N p) (fun Z => fineJob A (s.val\M) Z*backTo C.path N p hk (fineJob (ScenePack (N:=N) d x v) (s.val∩M)) Z)
  rw [back]
  apply congrArg
  funext Z
  have sep : Disjoint (s.val\M) (s.val∩M) := Finset.disjoint_left.mpr fun j hj hj' => (mem_sdiff.mp hj).2 (mem_inter.mp hj').2
  have split : (s.val\M)∪(s.val∩M)=s.val := by ext j; by_cases h : j∈M <;> simp [h]
  change (∏ j∈s.val,B j Z) = (∏ j∈s.val\M,A j Z)*(∏ j∈s.val∩M,P j Z)
  calc
    _ = ∏ j∈(s.val\M)∪(s.val∩M), B j Z := by rw [split]
    _ = _ := (prod_union sep).trans (congrArg₂ (·*·)
      (prod_congr rfl (fun j hj => by simp only [B,hybrid,(mem_sdiff.mp hj).2,if_false]; rfl))
      (prod_congr rfl (fun j hj => by simp only [B,hybrid,(mem_inter.mp hj).2,if_true]; rfl)))

private theorem reserve {b : ℝ} (hb : 4≤b) (t n h q : ℕ) :
    let a:=b^(t+2)
    let e:=((t+2)*n+1)*h
    2*(b^(q+e+1))⁻¹≤1 ∧ 2*(b^(q+e+1))⁻¹*(1+a^n)^h≤(b^q)⁻¹ := by
  dsimp only
  have b1 : 1≤b := by linarith
  have b0 : 0<b := zero_lt_one.trans_le b1
  let e := ((t+2)*n+1)*h
  have two : 2≤b := by linarith
  have low : 2≤b^(q+e+1) := two.trans (le_mul_of_one_le_left b0.le (one_le_pow₀ b1))
  constructor
  · rw [←div_eq_mul_inv,div_le_one (pow_pos b0 _)]
    exact low
  have room : 1+(b^(t+2))^n ≤ b^((t+2)*n+1) := by
    rw [←pow_mul,pow_succ]
    have h1 := one_le_pow₀ (n:=(t+2)*n) b1
    exact (show 1+b^((t+2)*n)≤b^((t+2)*n)*2 by linarith).trans
      (mul_le_mul_of_nonneg_left two (pow_nonneg b0.le _))
  have v := pow_le_pow_left₀ (by positivity : 0≤1+(b^(t+2))^n) room h
  have fit : (1+(b^(t+2))^n)^h≤b^e := v.trans_eq (pow_mul b _ h).symm
  calc
    _ ≤ b*(b^(q+e+1))⁻¹*b^e := mul_le_mul (mul_le_mul_of_nonneg_right two (by positivity)) fit (by positivity) (by positivity)
    _ = _ := by rw [pow_succ,pow_add]; field_simp

private theorem physical_rate (hC : C.Makes) {N p k : ℕ} (hk : k ≤ N) (q : ℕ) :
    ((C.path.levels.clock.hatBeta k)^q)⁻¹ ≤ 2^q*(Pert.Asymptotics.regulatorRun C N p k)^(2*q) := by
  let b := C.path.levels.clock.hatBeta k
  let a := C.path.β N p k
  have hb : 0 < b := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have rep := (hC.wilson.represents N p k hk).band
  have low : b/2 ≤ a := rep.1
  have high : a ≤ 2*b := rep.2
  have ha : 0 < a := (half_pos hb).trans_le low
  have rate : b⁻¹ ≤ 2*(Pert.Asymptotics.regulatorRun C N p k)^2 := by
    change b⁻¹ ≤ 2*(Real.sqrt a)⁻¹^2
    rw [inv_pow, Real.sq_sqrt ha.le]
    field_simp
    linarith only [high]
  rw [← inv_pow, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hb.le) rate q


/-- For every independent choice of indices to coarse-report, keep all other
microscopic signed labels on this same Wilson realization. The genuine selected
connected correlation, including all its mutually excluded partners, has uniform
O(g_R^(2q)) error on the native compactly separated report window. -/
theorem purchased [Fintype V] (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (Γ : Census V) (d : V→ℕ) {br : ℕ} (hbr : 0<br) (t q : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ dis : ℕ,(C.path.levels.budget k).B^8≤dis →
    (dis:ℝ)≤C.path.levels.clock.hatBeta k → ∀ N p, ∀ hk : k<N, ∀ x : V→Site (C.side k p),
    Sites26 (C:=C) br dis x → ∀ v : (j:V)→C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ M : Finset V, ∀ s : Γ.Mode,
    ‖(connected (microscopic Γ C (BarePack d x hk.le v))).part s-(connected (scheduled Γ M hk.le d x v)).part s‖ ≤
      (2*WilsonReportMomentDifference.multiplicity Γ s*2^q)*(Pert.Asymptotics.regulatorRun C N p k)^(2*q) := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  let n := Fintype.card V
  let h := Fintype.card (Hot Γ)
  let z := q+((t+2)*n+1)*h+1
  have grow := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [WilsonReportPartialShell.moments hG hC citizen d hbr t z,
    WilsonReportDisjointBack.entire hG hC citizen d,grow.eventually_ge_atTop 4,
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k paid back big refs
  intro dis lo hi N p hk x sites v inputs M s
  let A := BarePack d x hk.le v
  let F := hybrid M hk.le d x v
  let Z := fun j => backTo C.path N p hk.le (ScenePack (N:=N) d x v j)
  let b := C.path.levels.clock.hatBeta k
  let a := b^(t+2)
  let δ := (b^z)⁻¹
  have b1 : 1≤b := (C.path.levels.fits.delayed k).le
  have d0 : 0≤δ := inv_nonneg.mpr (pow_nonneg (zero_le_one.trans b1) _)
  have a1 : 1≤a := one_le_pow₀ b1
  have tariff := reserve big t n h q
  have full : hybrid (Finset.univ : Finset V) hk.le d x v=Z := by funext j; simp [hybrid,Z]
  have price := paid dis lo hi N p hk x sites v inputs
  have left (s') : ‖moment (C.beta N p) (fineJob A s')-moment (C.beta N p) (fineJob Z s')‖≤δ := by
    simpa only [full] using price univ s'
  have middle (s') : ‖moment (C.beta N p) (fineJob A s')-moment (C.beta N p) (fineJob F s')‖≤δ :=
    price M s'
  have bound (j U) : ‖Z j U‖≤a := by
    have gb := (cylinder_env (Strobe.bead_local H (x j) (v j) (refs j) hk.le (C.path.levels.budget k).B)).meas
    apply backTo_bound C.path N p hk.le gb a (fun V => ?_) U
    have h₁ := mul_le_mul (book.present k) (inputs j) (paid_pos C (d j) k N p (v j)) (zero_le_one.trans b1)
    exact (beadSize H citizen (v j) (x j) (C.path.levels.budget k).B hk (refs j) V).trans
      ((mul_le_mul big h₁ (mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge)
        (paid_pos C (d j) k N p (v j))) (zero_le_one.trans b1)).trans_eq (by dsimp only [a,b]; ring))
  let central := (connected (reported Γ C (N:=N) Z)).part s
  have compare (K : V → Config G (C.side N p)→ℂ)
      (cost : ∀ s',‖moment (C.beta N p) (fineJob K s')-moment (C.beta N p) (fineJob Z s')‖≤2*δ) :
      ‖(connected (microscopic Γ C K)).part s-central‖≤WilsonReportMomentDifference.multiplicity Γ s*(b^q)⁻¹ := by
    have test (u : Finset V) : ‖moment (C.beta N p) (fineJob K u)-
        (∫ U,fineJob Z u U ∂Therm.scene C.path N p N)‖≤2*δ := by
      rw [WilsonReportForwardTransfer.top hC]
      exact cost u
    have hgap := WilsonReportMomentDifference.original Γ C hC (k:=N) le_rfl K Z (mul_nonneg (by norm_num) d0)
      tariff.1 a1 bound test s
    exact hgap.trans ((mul_assoc _ _ _).le.trans (mul_le_mul_of_nonneg_left tariff.2
      (WilsonReportSeparatedMoments.count_nonneg Γ s)))
  have old := compare A (fun s' => (left s').trans (by linarith))
  have now := compare F (fun s' => by
    simpa only [dist_eq_norm,two_mul] using
      (dist_triangle (moment (C.beta N p) (fineJob F s')) (moment (C.beta N p) (fineJob A s'))
        (moment (C.beta N p) (fineJob Z s'))).trans (add_le_add
          (by simpa only [dist_eq_norm,norm_sub_rev] using middle s') (by simpa only [dist_eq_norm] using left s')))
  have geom := back N p hk.le x (fun j l diff => lo.trans (sites.apart j l diff)) v
  rw [←schedule_eq Γ M hk.le d x v geom]
  let oldVal := (connected (microscopic Γ C A)).part s
  let newVal := (connected (microscopic Γ C F)).part s
  have triangle : ‖oldVal-newVal‖≤2*(WilsonReportMomentDifference.multiplicity Γ s*(b^q)⁻¹) := by
    have other : ‖central-newVal‖≤WilsonReportMomentDifference.multiplicity Γ s*(b^q)⁻¹ := by
      rw [norm_sub_rev]; exact now
    exact (show ‖oldVal-newVal‖≤‖oldVal-central‖+‖central-newVal‖ by
      simpa only [dist_eq_norm] using dist_triangle oldVal central newVal).trans
        ((add_le_add old other).trans_eq (two_mul _).symm)
  exact triangle.trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (physical_rate hC hk.le q)
      (WilsonReportSeparatedMoments.count_nonneg Γ s)) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))

end YM.Integration.WilsonReportPartialCumulant
end

