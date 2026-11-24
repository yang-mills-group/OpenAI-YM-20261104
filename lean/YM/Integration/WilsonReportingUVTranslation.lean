import YM.Integration.WilsonReportingUVStencil

/-! Transfer each of the actual submitted child sites to the test of
the original single Wilson insertion under its own fine measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVTranslation
open Function Set Finset MeasureTheory Lattice Wilson RG Source RG12 OPE OPE.Therm
open RG05Readout Native Address Many Records Extra.Histories PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichFlatFibre WilsonReportingUVProbe WilsonReportingUVStencil Trace.Physical Push.Local
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p:ℕ) {m d:ℕ}

def fee {n:Side} (L:Rule n) (z:Site n):ℂ:= L (Pi.single z 1)

theorem sites {n:Side} (L:Rule n) (f:Site n→ℂ): L f=∑z,fee L z*f z := by
  have base:f=∑z:Site n,f z • Pi.single z (1:ℂ):=by
    funext z
    simp [Finset.sum_apply,Pi.single_apply]
  calc
    _=L (∑z:Site n,f z • Pi.single z (1:ℂ)):=congrArg L base
    _=∑z,fee L z*f z:=by simp only [map_sum,map_smul,fee,smul_eq_mul,mul_comm]

theorem transpose {n:Side} (β:ℝ) (X K:Goods G n) (z:Site n):
    (∫U,evaluate X U z*K U ∂law G n β)=∫U,X U*K (pull 1 (-z) U) ∂law G n β := by
  have back (A:Config G n):pull 1 (-z) (pull 1 z A)=A:=by
    simp only [pull_one]
    funext e
    simp [Lattice.translate,add_assoc]
  simpa only [evaluate,back] using
    (law_pull (G:=G) β 1 z).integral_comp (WardBin.Wheels.embedding_pull 1 z)
      (fun U=>X U*K (pull 1 (-z) U))

theorem test {n:Side} (β:ℝ) (X K:Goods G n) (xs:Continuous X) (ke:Envelope K) (L:Rule n):
    (∫U,L (evaluate X U)*K U ∂law G n β)=L (fun z=>∫U,X U*K (pull 1 (-z) U) ∂law G n β) := by
  have ei (z:Site n):Integrable (fun U=>fee L z*(evaluate X U z*K U)) (law G n β):=by
    have cont:Continuous (X ∘ pull 1 z):=xs.comp (continuous_pull (G:=G) 1 z)
    obtain ⟨B,cap⟩:=isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
    have en:Envelope (X ∘ pull 1 z):=⟨cont.measurable,B,fun U=>cap U (mem_univ _)⟩
    exact ((en.mulC ke).integrableC (law G n β)).const_mul _
  simp_rw [sites L,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum _ (fun z _=>ei z)]
  simp_rw [integral_const_mul,transpose]

def balanced (t:Letter d) (live:m≤N) (φ:Body):Rule (R.family.side N p):=
  weights R N p t live φ-(readJ t 0 φ*(R.family.S.a m:ℂ)^kept t) • atSite 0

theorem actual (t:Letter d) (x:R.family.label (kept t)) (live:m≤N) (φ:Body) (U:Config G (R.family.side N p)):
    residual R N p t x live φ U=balanced R N p t live φ (evaluate (R.family.O N p x 0) U):=by
  change WilsonReportingUVLikelihood.observable R N p t x live φ U-_ =_
  rw [microscopic]
  simp only [balanced,LinearMap.sub_apply,LinearMap.smul_apply,atSite,LinearMap.proj_apply,evaluate,pull_one]
  rw [show Lattice.translate 0 U=U from by funext e; simp [Lattice.translate]]
  rfl

theorem paired (t:Letter d) (x:R.family.label (kept t)) (live:m≤N) (φ:Body)
    (K:Goods G (R.family.side N p)) (bill:Envelope K):
    (∫U,residual R N p t x live φ U*K U ∂scene R.family.path N p N)=
      balanced R N p t live φ (fun z=>∫U,R.family.O N p x 0 U*K (pull 1 (-z) U) ∂scene R.family.path N p N) := by
  simp_rw [actual]
  let X:=R.family.O N p x 0
  let L:=balanced R N p t live φ
  let μ:=scene R.family.path N p N
  have eq:μ=law G (R.family.side N p) (R.family.beta N p):=WilsonMacroscopicForwardTransfer.top R.makes N p
  exact (congrArg (fun M:Measure (Config G (R.family.side N p))=>∫U,L (evaluate X U)*K U ∂M) eq).trans
    ((test _ X K (R.family.continuousO ..) bill L).trans
      (congrArg (fun M:Measure (Config G (R.family.side N p))=>L (fun z=>∫U,X U*K (pull 1 (-z) U) ∂M)) eq.symm))

end YM.Integration.WilsonReportingUVTranslation
