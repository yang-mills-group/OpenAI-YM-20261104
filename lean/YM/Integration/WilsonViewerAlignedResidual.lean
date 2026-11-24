import YM.Integration.WilsonCenteredAlignedPhysical
import YM.Integration.WilsonThermometerWeakValueRecovery

/-! Screened native sites norm a signed scalar on a separated compact. The
interpolation acts after the regulators and never divides by a cell volume. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonViewerAlignedResidual
open Function Filter Set Metric Finset Lattice Spec Extraction Table PhysMS OPE OPE.Orbits
open OPE.Stencils Trace.Pilot WilsonCenteredAlignedGeometry
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}

/-- The exact test sites used by the tensor stencil on an original schedule. -/
structure Pin (S:Schedule) (W:Finset E4) (r:ℝ) (s:ℕ) (o:Fin n → Cover) (y:Points n) : Prop where
  placed : ∀ i, r • y i = S.gridPoint s (o i)
  screened : Screen (fun i=>y i)
  residue : ∀i a, o i a % Cloud.count (Fin n) W = Cloud.residue W (S.a s/r) i a

def Nodes (S:Schedule) (W:Finset E4) (s:ℝ→ℕ) (F:ℝ→Points n→ℂ) (g:ℝ→ℝ) (q:ℕ) : Prop :=
  ∀ K, IsCompact K → K⊆conf n → ∃ C, 0≤C ∧ ∀ᶠ r in trail, ∀ o y, y∈K →
    Pin S W r (s r) o y → ‖F r y‖≤C*(g r)^q

/-- A fixed-order rooted tariff at each of the screened nodes buys the whole
compact. The source grid is independent of the spatial derivative order. -/
theorem values (S:Schedule) (W:Finset E4) (s:ℝ→ℕ) (F:ℝ→Points n→ℂ) (g:ℝ→ℝ) (q L:ℕ)
    (power:q≤2*(L+1)) (temperature:Tendsto g trail (𝓝 0)) (pos:∀ᶠr in trail,0<g r)
    (mesh:∀ᶠr in trail,S.a (s r)/r≤(g r)^2) (regular:∀ᶠr in trail,ContDiffOn ℝ (L+1) (F r) (conf n))
    (jets:WilsonThermometerWeakValueRecovery.Bounded trail (conf n) F (L+1))
    (samples:Nodes S W s F g q) :
    ∀ K, IsCompact K→K⊆conf n→∃ C, 0≤C ∧ ∀ᶠr in trail, ∀x∈K, ‖F r x‖≤C*(g r)^q := by
  intro K hk sep
  obtain ⟨R,rp,room⟩:=hk.exists_cthickening_subset_open (conf_open n) sep
  let K':=cthickening R K
  have hk':IsCompact K':=hk.cthickening
  obtain ⟨C,cp,pins⟩:=samples K' hk' room
  obtain ⟨B,bp,der⟩:=jets K' hk' room
  obtain ⟨D,dp,tensor⟩:=WilsonCenteredAlignedTensor.original (ι:=Coord n) L
  let M:ℝ:=(Cloud.count (Fin n) W:ℝ)
  have mp:0<M:=Int.cast_pos.mpr (Cloud.count_pos W)
  let pcap:=‖assemble n‖*(M*((L+1:ℕ)+3))
  have small:Tendsto (fun r=>pcap*g r^2) trail (𝓝 0):=by simpa only [zero_pow (by decide : 2≠0),mul_zero] using (temperature.pow 2).const_mul pcap
  let A:=B*‖assemble n‖^(L+1)*M^(L+1)
  have ap:0≤A:=by dsimp [A];positivity
  refine ⟨D*(C+A),mul_nonneg (zero_le_one.trans dp) (add_nonneg cp ap),?_⟩
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠr:ℝ in trail,0<r),pos,temperature.eventually_lt_const zero_lt_one,mesh,small.eventually_lt_const rp,
    regular,der,pins] with r r0 gp gu scaled tiny reg budget nodal x hx
  have rp0 : 0<r:=r0
  let h:=S.a (s r)/r
  have hp:0<h:=div_pos (S.a_pos _) r0
  let H:=step n W h
  have Hp:0<H:=positive n W hp
  have fits:‖assemble n‖*(H*((L+1:ℕ)+3))≤R:=by
    apply le_trans _ tiny.le
    have nonneg:0≤pcap:=by dsimp [pcap];positivity
    convert mul_le_mul_of_nonneg_left scaled nonneg using 1; dsimp [H,h,WilsonCenteredAlignedGeometry.step,pcap,M]; ring
  let origin:=chart x-offset W h
  let value:=fun y:Coord n→ℝ=>F r (shot W h y)
  have sample (y) (hy:valid (L+1) H (univ:Finset (Coord n)).toList origin y): ‖value y‖≤C*g r^q:=by
    have inside:=mem_cthickening_of_dist_le _ x R K hx ((full_tube W hp _ x y hy).trans fits)
    obtain ⟨o,sites,ok,res⟩:=grid W hp S (s r) (show r*h=S.a (s r) by dsimp[h];field_simp [rp0.ne']) _ origin y hy
    exact nodal o _ inside ⟨sites,ok,res⟩
  have slope:0≤B*‖assemble n‖^(L+1):=mul_nonneg bp (pow_nonneg (norm_nonneg _) _)
  have bounds:=tensor H (C*g r^q) (B*‖assemble n‖^(L+1)) Hp (mul_nonneg cp (pow_nonneg gp.le _)) slope origin value sample
  have measured:‖value origin‖≤D*(C*g r^q+B*‖assemble n‖^(L+1)*H^(L+1)):=by
    apply bounds
    intro y i hy
    let T:=H*((L+1:ℕ)+3)
    have tp:0<T:=mul_pos Hp (by positivity)
    have path (t) (ht:t∈Icc 0 T):shot W h y+t•unit i∈K':=
      mem_cthickening_of_dist_le _ x R K hx ((tube W hp (L+1) x y i hy ht).trans fits)
    obtain ⟨smooth,lineJet⟩:=WilsonCenteredAlignedPhysicalRegularity.line (conf_open n) (L+1) reg
      (shot W h y) (unit i) T tp (fun t ht=>room (path t ht))
    have same:(fun t:ℝ=>value (update y i (y i+t)))=fun t=>F r (shot W h y+t•unit i):=by
      funext t; dsimp[value];rw[line]
    rw [same]
    refine ⟨smooth,fun t ht=>?_⟩
    rw [lineJet t ht]
    let D':=iteratedFDeriv ℝ (L+1) (F r) (shot W h y+t•unit i)
    have action:‖D' (fun _=>unit i)‖≤‖D'‖*‖unit i‖^(L+1):=by simpa using D'.le_opNorm (fun _=>unit i)
    exact action.trans (mul_le_mul (budget _ (path t ht)) (pow_le_pow_left₀ (norm_nonneg _) (unit_bound i) _) (pow_nonneg (norm_nonneg _) _) bp)
  change ‖F r (shot W h origin)‖≤_ at measured
  rw [show shot W h origin=x from start W h x] at measured
  have powerFee:h^(L+1)≤g r^q:=(pow_le_pow_left₀ hp.le scaled _).trans ((pow_mul (g r) 2 (L+1)) ▸ pow_le_pow_of_le_one gp.le gu.le power)
  apply measured.trans
  calc
    _ =D*(C*g r^q+A*h^(L+1)):=by dsimp [A,H,WilsonCenteredAlignedGeometry.step,M];rw[mul_pow];ring
    _ ≤D*(C*g r^q+A*g r^q):=mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left powerFee ap)) (zero_le_one.trans dp)
    _ =D*(C+A)*g r^q:=by ring

end YM.Integration.WilsonViewerAlignedResidual
end
