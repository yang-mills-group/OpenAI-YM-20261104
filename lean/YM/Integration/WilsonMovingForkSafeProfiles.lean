import YM.Integration.WilsonMovingForkPositionIntegrals

/-! A single finite family of physical and independently positioned supports
on the selected moving aperture. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSafeProfiles
open Filter Set Lattice Source Spec Maxwell PhysMS FVA2 FVA2.Scale FVA2.Register FVA2.O.Project
open Trace.Pilot FVA2.O FVA2.O.Score FVA2.O.Enh MS MS.Land MS.Fleet MS.Theater MS.Rake
open WilsonMacroscopicRichMovingPlane WilsonMacroscopicRichTestGeometry WilsonPublicForkIndependentPlacement
open WilsonPublicForkTestProduct
open scoped Classical Topology
variable {G:Gauge}{n:ℕ}{I:Type}[Fintype I]

theorem original (simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)(A:ℕ)(ap:0<A)
    (K:Set (Points n))(compact:IsCompact K)(clear:K⊆conf n)(φ:I→Test 2):
    ∀ᶠr in trail,let t:=r/((g r)^A)^2
    let s:=age A (g r)
    ∀j,∀x∈K,∀z∈tsupport (φ j),placed r t x (relative z)∈conf (n+1) ∧
      forest x (squeeze (-s) (relative z))∈conf (n+1):=by
  change ∀ᶠr in trail,∀j,_
  apply eventually_all.mpr;intro j
  obtain ⟨δ,dp,safe⟩:=clearance K compact clear (φ j)
  have narrow:Tendsto (fun r=>((g r)^A)^2) trail (𝓝 0):=by
    simpa [zero_pow ap.ne'] using ((hg.conforms simple).pow A).pow 2
  filter_upwards [narrow.eventually (ge_mem_nhds dp),hg.positive,length_rate.pos] with r small gp rp
  let ρ:=((g r)^A)^2
  let t:=r/ρ
  let s:=age A (g r)
  have pos:0<ρ:=by dsimp [ρ];positivity
  have tp:0<t:=div_pos rp pos
  have qr:r/t=ρ:=by dsimp [t];field_simp;exact div_self rp.ne'
  have moved:(1:ℝ)/Real.exp s=ρ:=by rw [one_div,(same_clock ap gp).2,inv_inv]
  intro x hx z hz
  have first:=safe r t rp tp (qr ▸ small) x hx _ hz
  have second:=safe 1 (Real.exp s) zero_lt_one (Real.exp_pos s) (moved ▸ small) x hx _ hz
  have eq:forest x (squeeze (-s) (relative z))=placed 1 (Real.exp s) x (relative z):=by
    ext1 i;induction i using Fin.addCases <;> simp [placed,squeeze]
  exact ⟨first,eq ▸ second⟩

end YM.Integration.WilsonMovingForkSafeProfiles
