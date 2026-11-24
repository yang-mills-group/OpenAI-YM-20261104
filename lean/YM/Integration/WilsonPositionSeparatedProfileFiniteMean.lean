import YM.RG05Readout.Pulse.Excursion
import YM.RG05Readout.Harvest.Prices
import YM.Integration.ActualScalarTransport

/-! Stopping a genuine finite Wilson experiment under its original marginal
on any finite roster of positions and one common spatial test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileFiniteMean

open Function Filter Finset Set MeasureTheory Lattice Wilson RG OPE OPE.Therm
  RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten
  MergeProof Accent PhysicalNext.Repeat.Legato Bandage Labels Push.Local
open scoped Classical BigOperators Topology

variable {G : Gauge} (C : Family G) (hC : C.Makes)
  {I : Type} [DecidableEq I] [Fintype I] {N per b k : ℕ} (s : I→ℕ)
  (v : (i : I)→Palette C (s i)) (φ : Wave I) (r : ℝ) (m : ℕ)
  (top : b≤N) (stopped : k≤N) (g : Body)
local notation "Z" => Site (C.side b per)
local notation "raw" => constellation (C:=C) (p:=per) s v r φ top m
local notation "bud" => fun z : Z => restricted C b per z g
local notation "a" => C.S.a b

include hC in
private theorem ultraviolet (N per : ℕ) : scene C.path N per N=law G (C.side N per) (C.beta N per) := by
  unfold scene law dose weight
  rw [(hC.wilson.starts N per).2]

theorem registry (timely : ∀f:Body,Continuous (raw f)) {cap B : ℝ} (rp : 0<r)
    (enclosed : ∀ y∈tsupport φ.val,∀i,‖y i‖≤cap)
    (places : r*cap+2*a<C.S.radius per) (period : B+r*cap<C.S.radius per)
    (space : B+a<C.S.radius per) (support : ∀y∈Function.support g.val,‖y‖≤B) :
    moment (C.beta N per) (physicalEra r φ g C m per N s v)=
      (a:ℂ)^4*∑z:Z, moment (C.beta N per) (raw (bud z)) := by
  have geo := Pulse.registry (m:=m) s v r φ top rp enclosed places period g space support
  let μ := law G (C.side N per) (C.beta N per)
  let tree := C.S.toDepth top per
  let old (z : Z) := raw (bud z)
  have live (z : Z) : Integrable (old z) μ :=
    (timely _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have shift (z : Z) : Integrable (stepUp (1,false) (tree.embed z) (old z)) μ :=
    ((timely (bud z)).comp (Wilson.continuous_pull 1 (tree.embed z))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [geo]
  change (∫U,(a:ℂ)^4*(∑z:Z,stepUp (1,false) (tree.embed z) (old z)) U ∂μ)=_
  rw [integral_const_mul]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun z _=>shift z)]
  apply congrArg ((a:ℂ)^4*·)
  apply Finset.sum_congr rfl
  intro z _
  exact moment_pull _ 1 (tree.embed z) (old z) (live z)

include hC in
theorem marginal (timely : ∀f:Body,Continuous (raw f)) (z : Z) :
    moment (C.beta N per) (raw (bud z))=
    ∫U, actualTransport C (N:=N) (raw (bud z)) stopped U
       ∂ scene C.path N per k := by
  let X := raw (bud z)
  have timer := timely (bud z)
  have μ := ultraviolet C hC N per
  have weighted : Integrable (fun U=>(C.path.rep N per N).eval U • X U) (prior G _) := by
    simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow (N:=N) (p:=per) hC timer)
  rw [actualScene_transport C hC le_rfl weighted stopped,μ]
  rfl

theorem volume {B : ℝ} (space : B+a<C.S.radius per)
    (support : ∀y∈Function.support g.val,‖y‖≤B) :
    a^4*(∑z:Z,∫y in Native.box,‖(bud z).val y‖)=∫y,‖g.val y‖ := by
  let t (y : E4) : ℂ := (‖g.val y‖:ℂ)
  have smooth : Continuous g.val := (body_smooth g 1).continuous
  have whereat (y) (hy : y∈Function.support t) := support y (by
    apply Function.mem_support.mpr
    intro clear
    exact (Function.mem_support.mp hy) (by simp [t,clear]))
  have fixed := (coverings (C:=C) (p:=per) (b:=b) t (Complex.continuous_ofReal.comp smooth.norm) whereat space).2
  change a^4*(∑z:Z,∫y in Native.box,‖g.val (voyager C per b z y)‖)=_
  simpa only [t,integral_complex_ofReal,Complex.real_smul,←Complex.ofReal_pow,←Complex.ofReal_mul,
    ←Complex.ofReal_sum,Complex.ofReal_inj,←Finset.mul_sum] using fixed.symm

include hC in
theorem tested (timely : ∀f:Body,Continuous (raw f)) {cap B fee : ℝ} (rp : 0<r)
    (enclosed : ∀ y∈tsupport φ.val,∀i,‖y i‖≤cap)
    (places : r*cap+2*a<C.S.radius per) (period : B+r*cap<C.S.radius per)
    (space : B+a<C.S.radius per) (support : ∀y∈Function.support g.val,‖y‖≤B)
    (Y : Z → Config G (C.side k per)→ℂ)
    (finite : ∀z,Integrable (Y z) (scene C.path N per k))
    (price : ∀z, (∫U,‖actualTransport C (N:=N) (raw (bud z)) stopped U-Y z U‖
        ∂scene C.path N per k) ≤ fee*(∫y in Native.box,‖(bud z).val y‖)) :
    ‖moment (C.beta N per) (physicalEra r φ g C m per N s v)-
      (a:ℂ)^4*(∑z:Z,∫U,Y z U ∂scene C.path N per k)‖≤fee*(∫y,‖g.val y‖) := by
  let X (z : Z) := actualTransport C (N:=N) (raw (bud z)) stopped
  let μ := scene C.path N per k
  have lives (z : Z) : Integrable (X z) μ := by
    have weighted : Integrable (fun U=>(C.path.rep N per N).eval U • (raw (bud z)) U) (prior G _) := by
      simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow (N:=N) (p:=per) hC (timely (bud z)))
    exact actualScene_integrable_of_weighted C hC stopped
      (actualTransport_weighted_integrable_of_integrable C hC le_rfl weighted stopped)
  rw [registry C s v φ r m top g timely rp enclosed places period space support]
  simp_rw [marginal C hC s v φ r m top stopped g timely]
  rw [←mul_sub,←Finset.sum_sub_distrib,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (C.S.a_pos _).le,←volume C g space support]
  calc a^4 * ‖∑z:Z,((∫U,X z U ∂μ)-(∫U,Y z U ∂μ))‖ ≤ a^4 * (∑z:Z,fee*(∫y in Native.box,‖(bud z).val y‖)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (C.S.a_pos _).le _)
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro z _
        rw [←integral_sub (lives z) (finite z)]
        exact (norm_integral_le_integral_norm _).trans (price z)
       _ = _ := by rw [←Finset.mul_sum];ring

end YM.Integration.WilsonPositionSeparatedProfileFiniteMean
