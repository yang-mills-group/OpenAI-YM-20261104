import YM.Integration.WilsonMacroscopicRichRegister
import YM.Integration.WilsonPhysicalExteriorFrame

/-! A moving rich positive Gram tests raw retained labels at a polynomial
price. The price comes from the *actual* inverse leading frame and measured
Gram; no perturbative uniformity in the near cutoff is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingRichCharge
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Filter Set MeasureTheory Lattice Extraction Table Spec Climb OPE OPE.Orbits RG17 SharpGram PhysMS
open Trace.Pilot Frontier6.Road
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {V:Table C.book}

theorem fixed (F : Final C f V) (J : ℝ→tower V) (lead : Leading F J) (d:ℕ) :
    ∃ K:ℝ,0≤K ∧ ∀ᶠ τ in trail,∀ z:C.label d,
      ‖(J τ d).symm (V.project d z)‖≤K*τ^(-(d:ℝ)-1)*‖z‖ := by
  obtain ⟨H,H1,every⟩ := WilsonPhysicalExteriorFrame.between F d J lead 1 zero_lt_one
  obtain ⟨s,hs,sp⟩ := (every.and length_rate.pos).exists
  change 0<s at sp
  let A : C.label d →L[ℂ] (Bel C.book).Field d := ((J s d).symm.toLinearMap.comp (V.project d)).toContinuousLinearMap
  let t:= -(d:ℝ)-1
  let K:=H*(s^t)⁻¹*‖A‖
  have K0:0≤K := mul_nonneg (mul_nonneg (zero_le_one.trans H1) (inv_nonneg.mpr (Real.rpow_nonneg sp.le _))) A.opNorm_nonneg
  refine ⟨K,K0,?_⟩
  filter_upwards [length_rate.pos,((gt_mem_nhds sp).filter_mono nhdsWithin_le_nhds : ∀ᶠ τ:ℝ in trail,τ<s)] with τ tp upper z
  change 0<τ at tp
  have qt : τ/s ∈ Ioc (0:ℝ) 1 := ⟨div_pos tp sp,(div_le_one sp).mpr upper.le⟩
  have fromstep:=hs (τ/s) qt (V.project d z)
  rw [div_mul_cancel₀ τ sp.ne'] at fromstep
  calc
    _ ≤ H*(τ/s)^t*‖A z‖ := fromstep
    _ ≤ H*(τ/s)^t*(‖A‖*‖z‖) := mul_le_mul_of_nonneg_left (A.le_opNorm z)
      (mul_nonneg (zero_le_one.trans H1) (Real.rpow_nonneg qt.1.le _))
    _ = _ := by rw [Real.div_rpow tp.le sp.le];dsimp [K,t];ring

private theorem gram (B:Deck G) {O:Booked B} (M:MS_Data G O) (F : Final C f V) (J : ℝ→tower V)
    (lead:Leading F J) (d:ℕ) (φ:Test 2) :
    ∃ K:ℝ,0≤K ∧ ∀ᶠ τ in trail,∀ v:Glyph B d→ℂ,
      ‖(WilsonMacroscopicRichMeasuredGram.bank B F J d φ τ).vecMul v‖≤K*‖v‖ := by
  let A:=MSSeparatedTestGram.matrix M d 1 0 φ
  let N (j:Glyph B d):=∑ i:Glyph B d,(‖A i j‖+1)
  let K:=∑ j:Glyph B d,N j
  have nj (j:Glyph B d):0≤N j := Finset.sum_nonneg fun _ _=>add_nonneg (norm_nonneg _) zero_le_one
  have nk:0≤K := Finset.sum_nonneg fun j _=>nj j
  refine ⟨K,nk,?_⟩
  let Aτ:=WilsonMacroscopicRichMeasuredGram.bank B F J d φ
  have conv:=WilsonMacroscopicRichMeasuredGram.original B F J lead M d φ 1
  have entry (i j:Glyph B d) : ∀ᶠ τ in trail,‖Aτ τ i j‖≤‖A i j‖+1 := by
    have h: Tendsto (fun τ=>Aτ τ i j) trail (𝓝 (A i j)) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp conv i) j
    exact (h.norm.eventually (gt_mem_nhds (lt_add_one ‖A i j‖))).mono fun _ a=>a.le
  filter_upwards [Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (entry i))] with τ bounds v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg nk (norm_nonneg v))).mpr
  intro j
  have njk : N j≤K := Finset.single_le_sum (fun i _=>nj i) (Finset.mem_univ j)
  calc
    _ ≤ ∑ i:Glyph B d,‖v i*(Aτ τ i j)‖ := norm_sum_le _ _
    _ ≤ ∑ i:Glyph B d,‖v‖*(‖A i j‖+1) := Finset.sum_le_sum fun i _=>by
      rw [norm_mul];exact mul_le_mul (norm_le_pi_norm v i) (bounds i j) (norm_nonneg _) (norm_nonneg v)
    _=‖v‖*N j := by dsimp only [N];rw [Finset.mul_sum]
    _≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left njk (norm_nonneg v)

def read (B:Deck G) (F : Final C f V) (J : ℝ→tower V) (d:ℕ) (φ:Test 2) (τ:ℝ) : C.label d →L[ℂ] (Glyph B d→ℂ) :=
  let A:=WilsonMacroscopicRichMeasuredGram.bank B F J d φ τ
  let e:=WilsonMacroscopicRichFree.basis C B d
  (A.vecMulLinear.comp ((e.equivFun.toLinearMap.comp (J τ d).symm.toLinearMap).comp (V.project d))).toContinuousLinearMap

theorem original (B:Deck G) {O:Booked B} (M:MS_Data G O) (F : Final C f V) (J : ℝ→tower V)
    (lead:Leading F J) (d:ℕ) (φ:Test 2) :
    ∃ K:ℝ,0≤K ∧ ∀ᶠ τ in trail,‖read B F J d φ τ‖≤K*τ^(-(d:ℝ)-1) := by
  obtain ⟨H,H0,small⟩:=fixed F J lead d
  obtain ⟨K,K0,safe⟩:=gram B M F J lead d φ
  let e : (Bel C.book).Field d →L[ℂ] (Glyph B d→ℂ) :=
    (WilsonMacroscopicRichFree.basis C B d).equivFun.toLinearMap.toContinuousLinearMap
  let L:=K*‖e‖*H
  have L0:0≤L := mul_nonneg (mul_nonneg K0 e.opNorm_nonneg) H0
  refine ⟨L,L0,?_⟩
  filter_upwards [small,safe,length_rate.pos] with τ fixedτ gramτ tp
  let p:=τ^(-(d:ℝ)-1)
  apply (read B F J d φ τ).opNorm_le_bound (mul_nonneg L0 (Real.rpow_nonneg tp.le _))
  intro z
  let y:=(J τ d).symm (V.project d z)
  calc
    _ ≤ K*‖e y‖ := gramτ (e y)
    _ ≤ K*(‖e‖*‖y‖) := mul_le_mul_of_nonneg_left (e.le_opNorm y) K0
    _ ≤ K*(‖e‖*(H*p*‖z‖)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (fixedτ z) e.opNorm_nonneg) K0
    _=_ := by dsimp [p,L];ring

end YM.Integration.WilsonSeparatedMovingRichCharge
