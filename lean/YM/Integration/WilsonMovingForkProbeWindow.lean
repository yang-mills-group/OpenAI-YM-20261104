import YM.Integration.WilsonMovingForkPointHousing

/-! One native spatial margin for the whole determining family, including its
two-point input matrix, before the scalar source estimates are chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkProbeWindow
open Function Filter Set Finset OPE RG17 PhysMS
open Lattice Source Spec Maxwell FVA2 FVA2.Scale FVA2.Register Trace.Pilot MS MS.Land Pert.Asymptotics
open WilsonMacroscopicRichMovingPlane WilsonMacroscopicRichTestGeometry
open WilsonMovingForkPointHousing
open scoped Classical Topology
variable {I:Type}[Fintype I]{n:ℕ}{G:Gauge}

private theorem lower (u:I→ℝ)(positive:∀i,0<u i):∃q:ℝ,0<q ∧ ∀i,q≤u i:=by
  let p:=1+∑j,(u j)⁻¹
  have sp:0≤∑j,(u j)⁻¹:=Finset.sum_nonneg fun j _=>(inv_pos.mpr (positive j)).le
  have pp:0<p:=by dsimp[p];linarith
  refine ⟨p⁻¹,inv_pos.mpr pp,?_⟩
  intro i
  have one:(u i)⁻¹≤∑j,(u j)⁻¹:=Finset.single_le_sum (f:=fun j=>(u j)⁻¹)
    (fun j _=>(inv_pos.mpr (positive j)).le) (mem_univ i)
  have above:(u i)⁻¹≤p:=by dsimp[p];linarith
  simpa using inv_anti₀ (inv_pos.mpr (positive i)) above

theorem original (simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
    (K:Set (Points n))(compact:IsCompact K)(clear:K⊆conf n)(φ:I→Test 2):
    ∃M η:ℝ,0<M ∧ 0<η ∧ ∀A:ℕ,0<A → ∀ᶠr in trail,
      let t:=r/((g r)^A)^2
      ∀j:I,(∀x∈K,∀z∈tsupport (φ j),Fits r t M η (placed r t x (relative z))) ∧
        (∀z∈tsupport (φ j),Fits r t M η (t • z)):=by
  choose M η δ mp ep dp fit using fun j=>boxes K compact clear (φ j)
  obtain ⟨e,e0,eg⟩:=lower η ep
  obtain ⟨b,b0,bg⟩:=lower δ dp
  let roof:=1+∑j,M j
  have positive:0<roof:=add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun j _=>(mp j).le)
  have upper(j):M j≤roof:=by
    have:=Finset.single_le_sum (f:=M) (fun j _=>(mp j).le) (mem_univ j)
    dsimp[roof];linarith
  refine ⟨roof,e,positive,e0,?_⟩
  intro A ap
  have narrow:Tendsto (fun r=>((g r)^A)^2) trail (𝓝 0):=by
    simpa [zero_pow ap.ne'] using ((hg.conforms simple).pow A).pow 2
  filter_upwards [narrow.eventually (ge_mem_nhds b0),narrow.eventually (ge_mem_nhds zero_lt_one),
    hg.positive,length_rate.pos] with r small less gp rp
  let ρ:=((g r)^A)^2
  let t:=r/ρ
  intro t' j
  have pos:0<ρ:=by dsimp[ρ];positivity
  have tp:0<t:=div_pos rp pos
  have rt:r≤t:=by dsimp[t];apply (le_div_iff₀ pos).mpr;simpa using mul_le_mul_of_nonneg_left less rp.le
  have ratio:r/t=ρ:=by dsimp[t];field_simp;exact div_self rp.ne'
  have fields:=fit j r t rp rt (ratio ▸ small.trans (bg j))
  have promote {m:ℕ}{y:Points m}(f:Fits r t (M j) (η j) y):Fits r t roof e y:=
    ⟨fun i=>(f.1 i).trans (mul_le_mul_of_nonneg_right (upper j) tp.le),
      fun i k ik=>(eg j).trans (f.2 i k ik)⟩
  exact ⟨fun x hx z hz=>promote (fields.1 x hx z hz),fun z hz=>promote (fields.2 z hz)⟩

end YM.Integration.WilsonMovingForkProbeWindow
