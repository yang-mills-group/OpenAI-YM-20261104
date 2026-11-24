import YM.Integration.WilsonPhysicalMarkedDefectSingletonRent
import YM.Integration.WilsonOffsetSingleWallet
import YM.Integration.WilsonOffsetCommonConditional
import YM.MergeProof.South.Loft

/- The occupied word in the scalar unit disk is the original normalized
physical conditional of the actual housed basis field at its stated site.
At the appropriate admissible test the ultraviolet normalization cancels
exactly, on the whole input before conditioning. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Source Labels
open Next.Foundations ConnectedActivityE6 AllOrder AllOrder.Transit WheelP
open PhysicalNext.Repeat.Legato OPE OPE.Therm QuadraticLocal QuadraticLocal.Affinity
open Marker RG3.Annuncia MergeProof.Accent FVA1Physical.Round2.Curvature FVA1Physical.Round2.CP5
open scoped Topology BigOperators Classical

def family : Census Unit := Replica (fun _:Unit=>()) marks
abbrev Tests := Wallet (fun _:Unit=>chart ())
def test (c:ℂ) (hc:‖c‖≤1) : Tests := fun _=>⟨c,hc⟩
instance : Nonempty Tests := ⟨test 0 (by simp)⟩

variable {G:Gauge} {d:ℕ}
def basis {n:Side} (a:CoverLabel G d) (z:Site n) (U:Config G n) : ℂ :=
  (localSection G a.1.val).places (Pi.single a.2 1) z U

def source {n:Side} (a:CoverLabel G d) (z:Site n) (β:ℝ) (t:Tests) (U:Config G n) : Poly family :=
  Poly.inject (fun s : family.Mode => (∏ v∈s.val,(t v).val)*
    ∏ _v∈s.val, ((Coat.gStep β ^nativeGrade a)⁻¹:ℝ) • basis a z U)

theorem continuous_source {n:Side} (a:CoverLabel G d) (z:Site n) (β:ℝ) (t:Tests) :
    Continuous (source a z β t) := by
  apply continuous_pi
  intro s
  have field : Continuous (basis a z) := (localSection G a.1.val).continuous_places (Pi.single a.2 1) z
  have cost : Continuous (fun _ : Config G n => ((Coat.gStep β)^nativeGrade a)⁻¹) := continuous_const
  exact continuous_const.mul (continuous_finsetProd _ (fun _ _=>cost.smul field))

theorem occupied {n:Side} (a:CoverLabel G d) (z:Site n) (β:ℝ) (t:Tests) (U:Config G n) :
    (source a z β t U).part (family.fire ()) =
      (t ()).val * (((Coat.gStep β)^nativeGrade a)⁻¹:ℝ) • basis a z U := by
  change (∏v∈({()}:Finset Unit), (t v).val)*(∏ _v∈({()}:Finset Unit),
    (((Coat.gStep β)^nativeGrade a)⁻¹:ℝ) • basis a z U)=_
  simp [Complex.real_smul]

theorem admissible_weight (β:ℝ) (hot:1≤β) (h:ℕ) :
    ‖((Coat.gStep β ^h:ℝ):ℂ)‖≤1 := by
  have pos : 0<β := zero_lt_one.trans_le hot
  have small : Coat.gStep β≤1 := (inv_le_one₀ (Real.sqrt_pos.mpr pos)).mpr (by simpa using Real.sqrt_le_sqrt hot)
  have nonneg : 0≤Coat.gStep β := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg nonneg _)]
  exact pow_le_one₀ nonneg small

def originalTest (β:ℝ) (hot:1≤β) (h:ℕ) : Tests :=
  test ((Coat.gStep β ^h:ℝ):ℂ) (admissible_weight β hot h)

theorem bank {n:Side} (a:CoverLabel G d) (z:Site n) (β:ℝ) (hot:1≤β) (U:Config G n) :
    (source a z β (originalTest β hot (nativeGrade a)) U).part (family.fire ())=basis a z U := by
  have nz : Coat.gStep β ^nativeGrade a≠0 := (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hot))) _).ne'
  rw [occupied]
  change ((Coat.gStep β ^ nativeGrade a:ℝ):ℂ) * (((Coat.gStep β ^ nativeGrade a)⁻¹:ℝ):ℂ) • basis a z U=_
  have cz : ((Coat.gStep β ^ nativeGrade a:ℝ):ℂ)≠0 := by exact_mod_cast nz
  change ((Coat.gStep β ^ nativeGrade a:ℝ):ℂ) * ((((Coat.gStep β ^ nativeGrade a)⁻¹:ℝ):ℂ) * basis a z U)=_
  rw [Complex.ofReal_inv,←mul_assoc,mul_inv_cancel₀ cz,one_mul]

private theorem scalar_gust (A:History G) (N p b:ℕ) (f:Config G (A.S.side b p)→ℂ) {j:ℕ} (jb:j≤b):
    gust A N p b f j jb=Push.GridApprox.pushTo A N p jb f := by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,Push.GridApprox.pushTo_self]
  | of_succ z iz ih=>rw [gust_step A N p b f iz,Push.GridApprox.Birth.push_first A N p iz,ih]

theorem part (R:Run G) {N p b j:ℕ} (top:b≤N) (jb:j≤b) (f:Config G (R.family.side b p)→Poly family)
    (hf:Continuous f) (s:family.Mode) (U:Config G (R.family.side j p)) :
    (actualTransport R.family (N:=N) f jb U).part s =
      WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) jb (fun W=>(f W).part s) U := by
  letI : IsProbabilityMeasure (scene R.family.path N p b) := probability R.makes.wilson top
  have hF : Integrable f (scene R.family.path N p b) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have live := WilsonLimitConstruction.FundedWilsonTransportMoments.weighted R.family R.makes top hF
  let get := (Poly.get s).restrictScalars ℝ
  have each := get.integrable_comp hF
  refine Eq.trans ?_ (congrFun (WilsonOffsetCommonConditional.realized (C:=R.family) (N:=N) (p:=p)
    (j:=b) (k:=j) R.makes top jb (fun W=>(f W).part s) each) U).symm
  unfold actualTransport
  have moved := congrFun (gust_choose R.family.path N p (fun V=>(R.family.path.rep N p b).eval V • f V) live jb s) U
  have field : (fun V=>((R.family.path.rep N p b).eval V • f V).part s)=
      (fun V=>(R.family.path.rep N p b).eval V • (f V).part s) := funext fun V=> get.map_smul _ _
  rw [field,←scalar_gust] at moved
  exact (get.map_smul _ _).trans (congrArg (fun y:ℂ=>((R.family.path.rep N p j).eval U)⁻¹ • y) moved)

theorem physical (R:Run G) {N p b j:ℕ} (top:b≤N) (jb:j≤b) (a:CoverLabel G d) (z:Site (R.family.side b p))
    (hot:1≤(R.family.path.rep N p b).beta) (U:Config G (R.family.side j p)) :
    ((actualTransport R.family (N:=N) (source a z (R.family.path.rep N p b).beta
      (originalTest _ hot (nativeGrade a))) jb U).part (family.fire ())) =
      WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) jb (basis a z) U := by
  rw [part R top jb _ (continuous_source ..)]
  simp only [bank]

end YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
