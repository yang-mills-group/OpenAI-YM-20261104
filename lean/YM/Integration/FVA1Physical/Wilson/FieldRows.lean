import YM.Integration.FVA1Physical.Wilson.RowPurchase
import YM.Integration.FVA1Physical.Wilson.StationarySize
import YM.Integration.FVA1Physical.Sources.Round2.DistributedFields

/-! An absolute bound for the full outgoing normalized Wilson field coefficients.
The physical input can be a coincident or mixed product. The physical stationary
point, the full covariance and the distributed incoming action all use the same
gauge fixing. The cutoff precedes the period, forest, location and boundary ray. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology
variable {G:Gauge}

theorem outgoing_degree {σ:Type} [Fintype σ] [DecidableEq σ] (p m:ℕ)
    (Q src:PowerSeries (Pot σ)) (K:Matrix σ σ ℝ) (kind:Kind Q)
    (profile:Expanse Q m (p+1+p))
    (input:∀ i ≤ p+1+p, (PowerSeries.coeff i src).totalDegree ≤ m)
    (i:ℕ) (hi:i ≤ p) :
    (PowerSeries.coeff i (growP Q src K (p+1))).totalDegree ≤ m*(p+1+p)+2 := by
  have shifted:Expanse (Q+PowerSeries.X^(p+1)*src) m (p+1+p) := by
    refine ⟨fun j hj=>?_⟩
    rw [map_add]
    apply (MvPolynomial.totalDegree_add ..).trans (max_le (profile.profile j hj) ?_)
    rw [PowerSeries.coeff_X_pow_mul']
    split
    · expose_names
      have h1:1 ≤ j:=by omega
      exact (input _ ((Nat.sub_le ..).trans hj)).trans
        ((le_mul_of_one_le_right (Nat.zero_le m) h1).trans (by omega))
    · rw [MvPolynomial.totalDegree_zero]; omega
  have lo:=cohorts (k:=K) kind profile
  have hi':=cohorts (k:=K) (ripple kind src _ (Nat.succ_pos p)) shifted
  have le:p+1+i ≤ p+1+p:=by omega
  delta growP Scan
  rw [PowerSeries.coeff_mk,map_sub]
  exact (MvPolynomial.totalDegree_sub ..).trans ((max_le (hi'.profile _ le) (lo.profile _ le)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left m le) 2))

/-- Full rooted derivative rows of the normalized output Wilson coefficient of
every physical source in this finite field list, including the empty source.
All derivatives are evaluated at the genuine nonflat conditional mean. -/
theorem physical_field_rows {ι:Type} [Fintype ι] (I:ι→Lamp G)
    (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G) (p s q L:ℕ)
    (part:Bool) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Mosaic.Issue G) (b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      let d:=p+1+p
      Kind A.T → Expanse A.T 1 d → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s d →
      ∀ (z:Positions (Primary A.c G)), ‖z‖ ≤ A.fClock*D → ∀ (o:ι→Site A.f),
      (∀ j:Slice I, separation b (legs I o j).1 ≤ L*closeN y) →
      ∀ i ≤ p, Vault (address A.F G) {b} (αm y) s q (bulkPoint A z)
        (PowerSeries.coeff i (normalizedRows A χ (jointFieldBank I A o part) p)) (y^η) := by
  let d:=p+1+p
  let h:=d*d+2
  have hd:1 ≤ d:=by dsimp only [d]; omega
  obtain ⟨M,hM,bounded⟩:=purchased_stationary_size J clear simple H H' P K branch hD
  obtain ⟨δ,hδ,prices⟩:=purchased_normalized_rows J clear χ hχ simple H H' P K branch p d h s hd (half_pos hη)
  let R:=(1+M)^(h+1)
  have growth:=Work.E09.betaF_growth G P.L
  filter_upwards [prices,bounded,
    growth.eventually (field_vault_subpower I d s (h+2*Whisk.ribbon d d+1) L part hδ),
    ((tendsto_rpow_atTop (half_pos hη)).comp growth).eventually_ge_atTop R,
    growth.eventually_gt_atTop 0] with x price width fields reserve positive
  intro A b patch kernel season y d' kind plane bank z hz o near i hi
  let source:=jointFieldBank I A o part
  have raw:=fields A o b near
  have zero:=price A b patch kernel season kind plane bank source
    (fun j hj=>⟨(raw j hj).1,(raw j hj).2.trans hj⟩) i hi
  have slope:Expanse (barbed A.F A.v χ A.T) d d:=by
    refine ⟨fun j hj=>?_⟩
    have l:= (MSbar.Parma.expanseB A.F A.v χ d A.T plane).profile j hj
    simp only [one_mul] at l
    exact l.trans (Nat.add_le_add_right (le_mul_of_one_le_left (Nat.zero_le _) hd) 2)
  have hkind:Kind (barbed A.F A.v χ A.T):=by
    exact Rolling.well A.F A.v χ A.T kind
  have deg:=outgoing_degree p d _ source (fullCov A) hkind slope (fun j hj=>(raw j hj).2.trans hj) i hi
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have endpt:=Bout.across (bulkPoint A z) zero a0
    (by simpa only [sub_zero] using width A patch kernel season z hz) deg q
  apply Quote.widen endpt _ le_rfl
  calc y^(η/2)*(1+M)^(h+1) ≤ y^(η/2)*y^(η/2) :=
         mul_le_mul_of_nonneg_left reserve (Real.rpow_nonneg positive.le _)
       _ = y^η := by rw [←Real.rpow_add positive]; congr 1; ring

end YM.Integration.FVA1Physical.Wilson
