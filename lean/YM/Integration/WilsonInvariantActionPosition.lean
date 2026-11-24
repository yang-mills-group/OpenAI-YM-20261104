import YM.Integration.WilsonMovingReportDisplacement
import YM.Integration.WilsonReportBerthCurrency
import YM.Integration.WilsonReportCellProjection
import YM.Integration.WilsonMatrixTicketLanesReportedWindow

/-! All-order restoration of an actual raw physical Wilson moment from its
independently moved finest sites to the charged fine-grid ancestors. The fine
regulator limit is taken on the issued layout, after the radius is fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPosition
open Function Finset Filter Set Lattice Wilson RG Source Marker Extraction Spec
open Next.Rank PhysicalNext.Repeat.Legato RG17 FullVolume Table Climb Trace.Pilot
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}
    {n : ℕ} (L : Layout F)
    {B : ℕ} (hB : 0<B) (level : L.level = WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (g : ℝ→ℝ) (hg : Coupling G g)

private theorem finer (m s : ℕ) : ∃ k : ℕ, m<k ∧
    R.family.S.a k*(R.family.path.levels.clock.hatBeta m)^s ≤ R.family.S.a m := by
  let t := (R.family.path.levels.clock.hatBeta m)^s
  have h := R.family.S.shrinks.mul_const t
  exact ((eventually_gt_atTop m).and (h.eventually (ge_mem_nhds
    (show 0*t<R.family.S.a m from (zero_mul _).trans_lt (R.family.S.a_pos m))))).exists

/-- The first retained mesh beyond the prescribed precision. -/
def berth (s m : ℕ) : ℕ := Nat.find (finer R m s)

theorem arrival (s m : ℕ) : m<berth R s m ∧
    R.family.S.a (berth R s m)*(R.family.path.levels.clock.hatBeta m)^s ≤ R.family.S.a m :=
  Nat.find_spec (finer R m s)

include pace hB level hg in
theorem purchased (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J)
    {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d)
    (d : Caps n) (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n)
    (power debt q o : ℕ) (ho : n*power+debt+q+1 ≤ o) {ε:ℝ} (he : 0<ε) :
    ∀ᶠ r in Trace.Pilot.trail,let m := L.level r; let k := berth R (o+25) m
      let β := R.family.path.levels.clock.hatBeta m
      ∀ (v : (j:Fin n)→Free R.family (d j)) (w : R.family.book.Vector d),
      (∀ j,‖v j‖ ≤ β^power) → (∀ j,R.family.ref (d j) ≤ m) → (∀ j,master L (d j) r (w j)=J r (d j) (v j)) →
      ∀ᶠ i : ℕ×ℕ in L.lens,∀ hN:k ≤ i.1,∀ z : Positions n,
      r⁻¹ • tag (R.family.S.a i.1) z ∈ K →
      β^debt * ‖WilsonMovingReportDisplacement.read R L r d w i (WilsonReportCellProjection.ancestor (R.family.S.toDepth hN i.2) ∘ z) -
       WilsonMovingReportDisplacement.read R L r d w i z‖ ≤ ε*(g r)^q := by
  obtain ⟨M,a,hM,ha,all⟩ := WilsonMovingReportDisplacement.purchased R hG L J H paid d K hk sep
  have clock := WilsonReportBerthCurrency.purchased R hG pace hB g hg (n*power+debt) q hM (show 0<ε/2 by positivity) ha
  have mesh := WilsonMatrixTicketLanesReportedWindow.original R L hG pace hB level
  have grows : Tendsto (fun r=>R.family.path.levels.clock.hatBeta (L.level r)) trail atTop := by
    rw [level]
    exact (Station.hat_rate R.family.path.levels hG).comp
      (WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB)
  have large := grows.eventually_ge_atTop (4*n:ℝ)
  filter_upwards [all,clock,mesh,large,hg.positive,self_mem_nhdsWithin (a:=(0:ℝ))] with r sale pr window ample gp hr
  dsimp only
  let m := L.level r; let k := berth R (o+25) m; let β := R.family.path.levels.clock.hatBeta m
  have rp : 0<r := hr
  have bp : 0<β := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have ar : (β^o)⁻¹≤a ∧ M*β^(n*power+debt)*(β^o)⁻¹≤(ε/2)*(g r)^q := by
    simpa only [m,β,level] using pr o ho
  have basic : 1≤β := (R.family.path.levels.fits.delayed m).le
  have bill : (4*n:ℝ)≤β^25 := ample.trans (by
    simpa only [pow_one] using (pow_le_pow_right₀ basic (show 1≤25 by decide)))
  have ak : (4*n:ℝ)*R.family.S.a k≤r/β^o := by
    apply (le_div_iff₀ (pow_pos bp _)).mpr
    calc
      (4*n:ℝ)*R.family.S.a k*β^o ≤ β^25*R.family.S.a k*β^o :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right bill (R.family.S.a_pos k).le) (pow_nonneg bp.le _)
      _ = R.family.S.a k*β^(o+25) := by rw [pow_add]; ring
      _ ≤ R.family.S.a m := (arrival R (o+25) m).2
      _ ≤ r := window.1
  intro v w hv hf hw
  have fee : 0 < ε*(g r)^q/(4*β^debt) := by positivity
  have order := sale rp v w hf hw (ε*(g r)^q/(4*β^debt)) fee
  have vp : 0≤∏ j:Fin n,‖v j‖ := prod_nonneg fun _ _=>norm_nonneg _
  have size : (∏ j:Fin n,‖v j‖)≤β^(n*power) := by
    calc _ ≤ ∏ _j:Fin n, β^power := prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>hv j)
         _ = _ := by simp [←pow_mul,Nat.mul_comm]
  filter_upwards [order] with i step hN z hx
  let z' := WilsonReportCellProjection.ancestor (R.family.S.toDepth hN i.2) ∘ z
  let x := r⁻¹ • tag (R.family.S.a i.1) z
  let y := r⁻¹ • tag (R.family.S.a i.1) z'
  have close : ‖y-x‖≤(β^o)⁻¹ := by
    refine (WilsonReportCellProjection.relative R.family.S hN i.2 z rp).trans ?_
    apply (div_le_iff₀ rp).mpr
    simpa only [div_eq_mul_inv,mul_comm] using ak
  have exactx : tag (R.family.S.a i.1) z=r • x := by simp [x,smul_smul,rp.ne']
  have exacty : tag (R.family.S.a i.1) z'=r • y := by simp [y,smul_smul,rp.ne']
  have price := step x hx y (close.trans ar.1) z z' exactx exacty
  have dp := (pow_pos bp debt)
  have res : β^debt*(M*(∏ j,‖v j‖)*‖y-x‖) ≤ (ε/2)*(g r)^q := by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left size hM.le) close
      (norm_nonneg _) (mul_nonneg hM.le (pow_nonneg bp.le _))) dp.le).trans ?_
    rw [show β^debt*(M*β^(n*power)*(β^o)⁻¹)=M*β^(n*power+debt)*(β^o)⁻¹ by rw [pow_add];ring]
    exact ar.2
  refine (mul_le_mul_of_nonneg_left price.le dp.le).trans ?_
  rw [mul_add,show β^debt*(2*(ε*(g r)^q/(4*β^debt))) = ε*(g r)^q/2 by field_simp;ring]
  linarith

end YM.Integration.WilsonInvariantActionPosition
