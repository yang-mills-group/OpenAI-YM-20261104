import YM.Integration.ActualTrajectoryTransport
import YM.Integration.WilsonWeakStepPairing
import YM.Next.WARD_BIN.Haar
import YM.Next.WARD_BIN.Hats
import YM.Push.GRID_APPROXIMATION.Iterate
import YM.Integration.WilsonPlaquetteMoments
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Rebased


/-! Integrated bond equations of the original Wilson measure before arbitrary external observations along its genuine coarse history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonExteriorWardEquations
open Set MeasureTheory Filter Lattice Wilson RG OPE.Therm Push.GridApprox
open scoped Classical BigOperators Topology
variable {G : Gauge} {c f : Side}

/-- The genuine microscopic region used by these coarse observations, including their original finite choices. -/
def preimage (S : StepData c f) (X : Set (Site c)) : Set (Site f) :=
  {y | ∃ x ∈ X,y∈window (S.ratio.embed x) (reach S.patch)}

variable (C : Family G) (p : ℕ) {k j N : ℕ}

def region (r : k≤j) (X : Set (Site (C.side k p))) : Set (Site (C.side j p)) :=
  Nat.leRecOn (C:=fun i=>Set (Site (C.side i p))) r
    (fun {i}=>preimage (C.path.levels.clock.op i p)) X

theorem localized {ζ : Config G (C.side k p)→ℂ} {X : Set (Site (C.side k p))}
    (hζ : Envelope ζ) (hX : LocalOn X ζ) (q : k≤j) :
    LocalOn (region C p q X) (backTo C.path N p q ζ) := by
  induction j,q using Nat.le_induction with
  | base => simpa only [region,Nat.leRecOn_self,backTo_self] using hX
  | succ j q ih =>
    rw [backTo_next C.path N p q,show region C p (Nat.le_succ_of_le q) X=
      preimage (C.path.levels.clock.op j p) (region C p q X) by simp [region,Nat.leRecOn_succ q]]
    exact back_local (C.path.levels.blocks j p).branches (backTo_env C.path N p q hζ) ih _ _
      (fun x hx y hy=>⟨x,hx,hy⟩)

/-- Adjointness for the actual normalized marked field and the complete original backwards likelihood. -/
theorem adjoint (hC : C.Makes) {ζ : Config G (C.side k p)→ℂ} (hζ : Envelope ζ) (q : k≤j) :
    ∀ (_ : j≤N) (F : Config G (C.side j p)→ℂ), Envelope F →
    (∫ W,actualTransport C (N:=N) F q W*ζ W ∂scene C.path N p k)=
      ∫ U,F U*backTo C.path N p q ζ U ∂scene C.path N p j := by
  induction j,q using Nat.le_induction with
  | base => intro hj F _;rw [actualTransport_base C hC hj,backTo_self]
  | succ j q ih =>
    intro hj F hF
    have h1 : actualTransport C (N:=N) F (Nat.le_succ j)=actualAverage C (N:=N) F := by
      rw [actualTransport_step C hC hj F (Nat.lt_succ_self j),actualTransport_base C hC hj]
    have h2 := actualTransport_tower C hC hj F (Nat.le_succ j) q
    rw [h1] at h2
    rw [←h2,ih (Nat.le_of_lt hj) _ (WilsonForwardMeasurable.average hC hj hF),
      WilsonWeakStepPairing.forward hC hj (backTo_env C.path N p q hζ) hF,backTo_next C.path N p q]

private theorem constant {n : Side} {Y : Set (Site n)} {g : Config G n→ℂ} (hg : LocalOn Y g)
    {e : Edge (Site n)} (away : e.1∉Y) (a : G.Color) (U : Config G n) :
    g (WardBin.slide e U a)=g U := by
  apply hg
  intro w hw _
  have hwe : w≠e := by rintro rfl;exact away hw
  simp [WardBin.slide,Function.update_of_ne hwe]

/-- For any observed subset of the coarse torus and any bounded Borel exterior, the complete original Wilson bond discrepancy vanishes through every genuine intermediate projection. -/
theorem original (hC : C.Makes) (q : k≤N) {X : Set (Site (C.side k p))}
    {ζ : Config G (C.side k p)→ℂ} (hζ : Envelope ζ) (hX : LocalOn X ζ)
    (e : Edge (Site (C.side N p))) (away : e.1∉region C p q X)
    (V : Config G (C.side N p)→WardBin.Covector G)
    (hV : ∀ i,WardBin.HasFlow e (WardBin.dirs G i) fun U => V U (WardBin.dirs G i)) :
    (∫ W,actualTransport C (N:=N) (WardBin.equation (C.beta N p) e V) q W*ζ W ∂scene C.path N p k)=0 := by
  let B := backTo C.path N p q ζ
  have hB : Envelope B := backTo_env C.path N p q hζ
  have ht (a : G.Color) (U : Config G (C.side N p)) : B (WardBin.slide e U a)=B U :=
    constant (localized C p hζ hX q) away a U
  have hE := WardBin.equation_bounded hV (C.beta N p)
  rw [adjoint C p hC hζ q le_rfl _ hE,onstage hC.wilson _ (WardBin.bound_int (hE.mulC hB) _)]
  exact WardBin.ward_null hV _ (WardBin.rated hC p N).1.ne' hB ht

end YM.Integration.WilsonExteriorWardEquations
end


/-! The first colour contraction of the physical Wilson bond equation, for every two-index tensor, measured external Borel observation, and genuine regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPlaquetteWardTrace
open Filter Set MeasureTheory Lattice Wilson RG Push.GridApprox OPE.Therm
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side}

abbrev Form (G : Gauge) := G.Color →L[ℝ] G.Color →L[ℝ] ℂ

def edge (z : Face (Per n)) : Edge (Site n) := (z.1,z.2.val.1)

def differential (a : G.Color) (u : G.El) := G.projectColor (G.colorMat a*G.mat u)

theorem based (a : G.Color) (u : G.El) :
    HasDerivAt (fun t : ℝ=>G.curvature (WardBin.left a u t)) (differential a u) 0 := by
  simp only [SelectedOrderedKernels.Selected.curvature_project,differential]
  exact G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (WardBin.matLeft_zero a u)

theorem chord (a : G.Color) (u : G.El) : ‖differential a u-a‖≤G.colorScale*‖a‖*G.chord u := by
  have he : differential a u-a=G.projectColor (G.colorMat a*(G.mat u-1)) := by
    simp only [differential,mul_sub,mul_one,map_sub,G.project_colorMat]
  have hn : ‖G.mat u-1‖=G.colorScale*G.chord u := by
    unfold Gauge.chord
    change ‖G.mat u-1‖=G.colorScale*(‖G.mat u-1‖/G.colorScale)
    field_simp [G.colorScale_pos.ne']
  rw [he]
  calc
    _ ≤ ‖G.colorMat a*(G.mat u-1)‖/G.colorScale := G.project_norm _
    _ ≤ (‖G.colorMat a‖*‖G.mat u-1‖)/G.colorScale := div_le_div_of_nonneg_right (norm_mul_le _ _) G.colorScale_pos.le
    _ = _ := by rw [G.colorMat_norm,hn];field_simp [G.colorScale_pos.ne']

private theorem wrap_distinct (hn : 1<n.val) (x : Site n) (i : Axis) : x+step i≠x := by
  letI : Nontrivial (ZMod n.val) := ZMod.nontrivial_iff.mpr (by omega)
  intro h
  have h' := congrFun h i
  simp [step_apply] at h'

/-- One genuine based plaquette reads its first edge exactly once on an actual nondegenerate side. -/
theorem shifted (hn : 1<n.val) (z : Face (Per n)) (U : Config G n) (a : G.Color) (t : ℝ) :
    faceValue (WardBin.slide (edge z) U (t•a)) z=WardBin.left a (faceValue U z) t := by
  have h₁ : (z.1+step z.2.val.1,z.2.val.2)≠edge z := by
    intro h;exact z.2.prop.ne (congrArg Prod.snd h).symm
  have h₂ : (z.1+step z.2.val.2,z.2.val.1)≠edge z := by
    intro h;exact wrap_distinct hn z.1 z.2.val.2 (congrArg Prod.fst h)
  have h₃ : (z.1,z.2.val.2)≠edge z := by
    intro h;exact z.2.prop.ne (congrArg Prod.snd h).symm
  have wheel (A : Config G n) : faceValue A z=WardBin.wheel (edge z) (posDir z.2.val.2) A := by
    rfl
  simp only [wheel,WardBin.wheel_pos,WardBin.slide,WardBin.left,edge,Function.update_self,mul_assoc]
  unfold edge at h₁ h₂ h₃
  rw [Function.update_of_ne h₁,Function.update_of_ne h₂,Function.update_of_ne h₃]

def covector (L : Form G) (z : Face (Per n)) (U : Config G n) : WardBin.Covector G :=
  L (G.curvature (faceValue U z))

def measuredTrace (L : Form G) (z : Face (Per n)) (U : Config G n) : ℂ :=
  ∑ i,L (differential (WardBin.dirs G i) (faceValue U z)) (WardBin.dirs G i)

def trace (L : Form G) : ℂ := ∑ i,L (WardBin.dirs G i) (WardBin.dirs G i)

def rate (L : Form G) : ℝ := (Fintype.card G.ColorIndex:ℝ)*‖L‖*G.colorScale

private theorem directional (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (a : G.Color) (U : Config G n) :
    HasDerivAt (fun t : ℝ=>covector L z (WardBin.slide (edge z) U (t•a)) a)
      (L (differential a (faceValue U z)) a) 0 := by
  simp only [covector,shifted hn]
  exact (L.flip a).hasFDerivAt.comp_hasDerivAt 0 (based a (faceValue U z))

private theorem c_diff (a : G.Color) : Continuous (differential a) :=
  G.projectColor.continuous_of_finiteDimensional.comp (continuous_const.mul G.continuous_mat)

private theorem c_face (z : Face (Per n)) : Continuous (fun U : Config G n=>faceValue U z) := by
  unfold faceValue;fun_prop

theorem flows (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (i : G.ColorIndex) :
    WardBin.HasFlow (edge z) (WardBin.dirs G i) fun U=>covector L z U (WardBin.dirs G i) := by
  let a:=WardBin.dirs G i
  have slope (U : Config G n) : WardBin.slope (edge z) a (fun V=>covector L z V a) U=
      L (differential a (faceValue U z)) a := (directional hn L z a U).deriv
  refine ⟨WardBin.envelope_continuous ((L.flip a).continuous.comp (G.continuous_curvature.comp (c_face z))),?_,
    fun U=>(directional hn L z a U).differentiableAt⟩
  change Envelope (WardBin.slope (edge z) a (fun V=>covector L z V a))
  rw [show WardBin.slope (edge z) a (fun V=>covector L z V a)=(fun U=>L (differential a (faceValue U z)) a) from funext slope]
  exact WardBin.envelope_continuous ((L.flip a).continuous.comp ((c_diff a).comp (c_face z)))

theorem divergence (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (U : Config G n) :
    WardBin.divergence (edge z) (covector L z) U=measuredTrace L z U := by
  unfold WardBin.divergence measuredTrace
  exact Finset.sum_congr rfl fun i _=>(directional hn L z (WardBin.dirs G i) U).deriv

theorem pointwise (L : Form G) (z : Face (Per n)) (U : Config G n) :
    ‖measuredTrace L z U-trace L‖≤rate L*G.chord (faceValue U z) := by
  let P:=faceValue U z
  let A:=WardBin.dirs G
  have one (i : G.ColorIndex) : ‖A i‖=1 := OrthonormalBasis.norm_eq_one ..
  have summand (i : G.ColorIndex) :
      ‖L (differential (A i) P) (A i)-L (A i) (A i)‖≤‖L‖*G.colorScale*G.chord P := by
    rw [show L (differential (A i) P) (A i)-L (A i) (A i)=L (differential (A i) P-A i) (A i) by rw [map_sub];rfl]
    apply ((L (differential (A i) P-A i)).le_opNorm (A i)).trans
    rw [one i,mul_one]
    apply (L.le_opNorm _).trans
    simpa only [one i,mul_one,mul_assoc] using mul_le_mul_of_nonneg_left (chord (A i) P) (norm_nonneg L)
  unfold measuredTrace trace
  rw [←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _=>summand i)).trans_eq ?_)
  simp [rate, nsmul_eq_mul];ring

theorem trace_env (L : Form G) (z : Face (Per n)) : Envelope (fun U : Config G n=>measuredTrace L z U-trace L) := by
  apply WardBin.envelope_continuous
  apply Continuous.sub _ continuous_const
  exact continuous_finsetSum _ fun i _=>(L.flip (WardBin.dirs G i)).continuous.comp ((c_diff _).comp (c_face z))

variable (C : Family G) (hC : C.Makes) {N p j : ℕ}
local notation "nf" => C.side N p
local notation "β" => C.beta N p
local notation "μ" => scene C.path N p N
include hC

/-- Independent trace and measured native Wilson curvature paired with the entire original colour Euler field. -/
theorem response (q : j≤N) {X : Set (Site (C.side j p))} {ζ : Config G (C.side j p)→ℂ}
    (hζ : Envelope ζ) (hX : LocalOn X ζ) (L : Form G) (z : Face (Per nf))
    (away : (edge z).1∉WilsonExteriorWardEquations.region C p q X) :
    (∫ W,actualTransport C (N:=N) (fun U=>(β:ℂ)*L (G.curvature (faceValue U z)) (WardBin.euler U (edge z))-trace L) q W*ζ W
        ∂scene C.path N p j) = ∫U,(measuredTrace L z U-trace L)*backTo C.path N p q ζ U ∂μ := by
  let A:=covector L z
  let E:=WardBin.equation β (edge z) A
  let D:=fun U : Config G nf=>measuredTrace L z U-trace L
  let B:=backTo C.path N p q ζ
  have hn : 1<(C.side N p).val := lt_of_lt_of_le (by decide : 1<4) (Next.Foundations.actual_side_ge C.S N p)
  have hb : (β:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (WardBin.rated hC p N).1.ne'
  have hE : Envelope E := WardBin.equation_bounded (flows hn _ _) _
  have hD : Envelope D := trace_env _ _
  have hB : Envelope B := backTo_env C.path N p q hζ
  have hU : (fun U=>(β:ℂ)*L (G.curvature (faceValue U z)) (WardBin.euler U (edge z))-trace L)=
      (fun U=>(β:ℂ)*E U+D U) := by
    funext U;dsimp [E,D,A,WardBin.equation,covector];rw [divergence hn];field_simp [hb];ring
  rw [hU,WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ ((Envelope.constC (β:ℂ)).mulC hE|>.addC hD)]
  have null := WilsonExteriorWardEquations.original C p hC q hζ hX (edge z) away A (flows hn L z)
  rw [WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ hE] at null
  letI : IsProbabilityMeasure μ := probability (H:=C.path) (p:=p) hC.wilson le_rfl
  change (∫U,((β:ℂ)*E U+D U)*B U ∂μ)=∫U,D U*B U ∂μ
  simp_rw [add_mul,mul_assoc]
  rw [integral_add (((hE.mulC hB).integrableC _).const_mul _) ((hD.mulC hB).integrableC _),integral_const_mul]
  change (∫U,E U*B U ∂μ)=0 at null
  rw [null,mul_zero,zero_add]

/-- One original cutoff before all tori, colour tensors, ordered plaquettes and separated coarse observations. -/
theorem original (P : Poetry C.path.levels) (hG : G.Simple) {s : ℝ} (hs : s<1) :
    ∀ᶠ N : ℕ in atTop, ∀ p j (q : j≤N) (L : Form G) (z : Face (Per (C.side N p)))
      (X : Set (Site (C.side j p))) (ζ : Config G (C.side j p)→ℂ), Measurable ζ → (∀ W,‖ζ W‖≤1) →
      LocalOn X ζ → (edge z).1∉WilsonExteriorWardEquations.region C p q X →
    ‖∫ W,actualTransport C (N:=N) (fun U=>(C.beta N p:ℂ)*L (G.curvature (faceValue U z)) (WardBin.euler U (edge z))-trace L) q W*ζ W
        ∂scene C.path N p j‖ ≤ 3*rate L*(C.path.levels.clock.hatCoupling N)^s := by
  filter_upwards [rare P hG hC.wilson,WilsonCurvatureRankRate.thermal C.path.levels hG 1 (s:=s) (by simpa only [Nat.cast_one] using hs)] with N hr h
  intro p j q L z X ζ hm hb hx away
  have hζ : Envelope ζ := ⟨hm,1,hb⟩
  rw [response C hC q hζ hx L z away]
  letI : IsProbabilityMeasure (scene C.path N p N) := probability (H:=C.path) (p:=p) hC.wilson le_rfl
  let D := fun U : Config G (C.side N p)=>(measuredTrace L z U-trace L)*backTo C.path N p q ζ U
  have hD (U) : ‖D U‖≤rate L*(G.chord (faceValue U z))^1 := by
    rw [pow_one];exact (le_of_eq (norm_mul _ _)).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (backTo_bound C.path N p q hm 1 hb U)).trans (pointwise L z U))
  have hR : 0≤rate L := by unfold rate;positivity [G.colorScale_pos]
  refine (norm_integral_le_integral_norm _).trans ((WilsonPlaquetteMoments.weighted _ z 1 h.1
    (hr N le_rfl p z) hR (fun U=>‖D U‖) (fun U=>norm_nonneg _) hD).trans ?_)
  have h1 : cool C.path.levels N≤(C.path.levels.clock.hatCoupling N)^s := by simpa only [pow_one] using h.2.1
  rw [pow_one,pow_one];nlinarith [mul_le_mul_of_nonneg_left h1 hR,mul_le_mul_of_nonneg_left h.2.2 hR]

end YM.Integration.WilsonPlaquetteWardTrace
end


/-! The explicitly nonzero fully contracted original two-curvature coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWardMetric
open Set Filter MeasureTheory Lattice Wilson RG OPE.Therm Push.GridApprox WilsonPlaquetteWardTrace
open scoped Classical BigOperators Topology InnerProductSpace
variable {G : Gauge}

def metric (G : Gauge) : Form G :=
  ((ContinuousLinearMap.compL ℝ G.Color ℝ ℂ) Complex.ofRealCLM).comp (innerSL ℝ)

theorem apply_metric (a b : G.Color) : metric G a b=(inner ℝ a b : ℝ) := rfl

theorem metric_trace : trace (metric G)=(Fintype.card G.ColorIndex:ℂ) := by
  unfold trace;simp only [apply_metric,real_inner_self_eq_norm_sq,OrthonormalBasis.norm_eq_one,one_pow,Complex.ofReal_one]
  simp

/-- The coefficient is the original colour dimension, uniformly before the true torus period and plaquette. -/
theorem physical (C : Family G) (hC : C.Makes) (P : Poetry C.path.levels) (hG : G.Simple) {s : ℝ} (hs : s<1) :
    ∀ᶠ N : ℕ in atTop, ∀ p (z : Face (Per (C.side N p))),
    ‖(C.beta N p:ℂ)*(∫U,(inner ℝ (G.curvature (faceValue U z)) (WardBin.euler U (edge z)):ℝ) ∂scene C.path N p N : ℝ)-
      (Fintype.card G.ColorIndex:ℂ)‖ ≤ 3*rate (metric G)*(C.path.levels.clock.hatCoupling N)^s := by
  filter_upwards [WilsonPlaquetteWardTrace.original C hC P hG hs] with N hh
  intro p z
  haveI : IsProbabilityMeasure (scene C.path N p N) := probability (H:=C.path) (p:=p) hC.wilson le_rfl
  let I (U : Config G (C.side N p)) : ℝ := inner ℝ (G.curvature (faceValue U z)) (WardBin.euler U (edge z))
  have hc : Continuous I := by dsimp [I];unfold faceValue;fun_prop
  have hi : Integrable (fun U=>((I U):ℂ)) (scene C.path N p N) :=
    WardBin.bound_int (WardBin.envelope_continuous (Complex.continuous_ofReal.comp hc)) _
  have away : (edge z).1∉WilsonExteriorWardEquations.region C p (le_refl N) (∅ : Set (Site (C.side N p))) := by
    simp [WilsonExteriorWardEquations.region,Nat.leRecOn_self]
  have h := hh p N le_rfl (metric G) z ∅ (fun _=>1) measurable_const (fun _=>by simp)
    (fun _ _ _=>rfl) away
  rw [actualTransport_base C hC le_rfl] at h
  simp only [apply_metric,metric_trace,mul_one] at h
  change ‖∫ U,(C.beta N p:ℂ)*(I U:ℂ)-(Fintype.card G.ColorIndex:ℂ) ∂scene C.path N p N‖≤_ at h
  rw [integral_sub (hi.const_mul _) (integrable_const _),integral_const_mul,integral_complex_ofReal,
    integral_const,probReal_univ,one_smul] at h
  exact h

end YM.Integration.WilsonWardMetric
end
