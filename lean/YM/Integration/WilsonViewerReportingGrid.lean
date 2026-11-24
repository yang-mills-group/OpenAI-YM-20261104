import YM.Integration.WilsonAddressedReportingMesh

/-! One paid original reporting grid for an arbitrary finite horizon. The original
station and its basis are chosen before positions, the requested order or the test. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonViewerReportingGrid
open Function Filter Set RG Wilson Extraction Table Spec Trace.Pilot GapsContact.Seams
open GapsContact.Ascent Trace.Terrace
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourPool WilsonAddressedReportingScale
open scoped Classical Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) {ℓ : Ultrafilter (ℕ×ℕ)} {Y : (Climb.Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family}
local notation "C₀" => R.family

structure Grid (H : ℕ) (g : ℝ → ℝ) where
  stage : ℕ
  allowance : ℝ
  positive : 0<allowance
  date : ℝ → ℕ
  width : ℝ → ℕ
  plots : ∀ᶠ r in trail, Receipt F ℓ (radius stage r) (date r) (width r) H (dock (radius stage r)^stage)
  upper : ∀ᶠ r in trail, (C₀).S.a (date r)/r ≤ (g r)^2
  inverse : ∀ᶠ r in trail, (r/(C₀).S.a (date r))*(g r)^(2*(2*stage+2)) ≤ allowance

theorem original (simple : G.Simple) (bliss : Bliss F ℓ arch Y) (g : ℝ → ℝ) (temp : Coupling G g)
    (H : ℕ) : Nonempty (Grid (ℓ:=ℓ) F H g) := by
  classical
  obtain ⟨T,receipts⟩:=WilsonThermometerUnitFilingFourPool.original F simple bliss H
  let offered (r : ℝ) (p:ℕ×ℕ) := Receipt F ℓ (radius T r) p.1 p.2 H (dock (radius T r)^T)
  have available : ∀ᶠ r in trail, ∃ p, offered r p := by
    filter_upwards [(near T).eventually receipts] with r sold
    obtain ⟨j,m,hm⟩:=sold
    exact ⟨(j,m),hm⟩
  let p (r:ℝ):=Classical.epsilon (offered r)
  have sold : ∀ᶠ r in trail, offered r (p r) :=available.mono fun _ yes=>Classical.epsilon_spec yes
  obtain ⟨U,u,prices⟩:=WilsonAddressedReportingMesh.priced F ℓ simple g temp T
  have charged:=prices.and sold |>.mono fun r yes=>yes.1 T le_rfl _ _ _ yes.2
  exact ⟨⟨T,U,u,fun r=>(p r).1,fun r=>(p r).2,sold,charged.mono fun _ h=>h.1,charged.mono fun _ h=>h.2⟩⟩

/-- A complete linear source map for a grade. Its very same cutoff cylinder can be
translated to all sites and used in all finite differences and reflections. -/
theorem labels {r B:ℝ} {j m d:ℕ} (arm:BookedArm F ℓ r j m d B) :
    ∃ (b:S.Field d →ₗ[ℂ] (C₀).label d) (w:(ℕ×ℕ) → S.Field d →ₗ[ℂ] (C₀).label d),
      (∀ v, S.project d (b v)=v) ∧
      (∀ v, Tendsto (fun u=>w u v) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b v))) ∧
      ∀ v, (∀ N p, j<N → Next.UVStress.quota (C₀) d j N p (w (N,p) v) ≤
        (C₀).S.a j^d*B*cost F d r v) ∧
        ∀ᶠ u:ℕ×ℕ in f.fuse, OPE.Cards.PaidAt (C₀).S u.1 u.2 m ((C₀).beta u.1 u.2)
          (B*cost F d r v) ((C₀).O u.1 u.2 (w u v) 0) := by
  obtain ⟨V,k,live,T,Z,_,_,projection,travel,paid⟩:=arm.station
  let b:=Z.toLinearMap.comp T.symm.toLinearMap
  let w (u:ℕ×ℕ):=(heightV V k d u).toLinearMap.comp T.symm.toLinearMap
  refine ⟨b,w,?_,?_,?_⟩
  · intro v
    exact (projection (T.symm v)).trans (T.apply_symm_apply v)
  · intro v
    exact (ContinuousLinearMap.apply ℂ _ (T.symm v)).continuous.tendsto Z |>.comp travel
  · intro v
    simpa only [w,heightV,dif_pos live,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe,T.apply_symm_apply] using paid (T.symm v)

end YM.Integration.WilsonViewerReportingGrid
end
