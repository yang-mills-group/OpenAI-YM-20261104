import YM.Integration.WilsonOriginalWardResponse
import YM.Lattice.Support
import YM.Next.MULTISOURCE.Wage


/-! Authentic four oriented occurrences of a plaquette and an exterior path avoiding whichever single bond is varied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPlaquetteIncidence
open Set Function Lattice Wilson RG
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge}

def edges (z : Face (Per n)) : Fin 4 → Edge (Site n) :=
  ![(z.1,z.2.val.1),(z.1+step z.2.val.1,z.2.val.2),(z.1+step z.2.val.2,z.2.val.1),(z.1,z.2.val.2)]

def sign : Fin 4 → ℝ := ![1,1,-1,-1]

def curl (z : Face (Per n)) (v : Edge (Site n) → ℝ) := ∑ i:Fin 4, sign i*v (edges z i)

def headed {K : Type*} [Group K] (a : Fin 4 → K) : Fin 4 → K :=
  ![a 0*a 1*(a 2)⁻¹*(a 3)⁻¹, a 1*(a 2)⁻¹*(a 3)⁻¹*a 0,
    a 2*(a 1)⁻¹*(a 0)⁻¹*a 3, a 3*a 2*(a 1)⁻¹*(a 0)⁻¹]

def sideHead (z : Face (Per n)) (i : Fin 4) (U : Config G n) := headed (fun k => U (edges z k)) i

private theorem step_ne (hn : 1<n.val) (x : Site n) (i : Axis) : x+step i≠x := by
  letI : Nontrivial (ZMod n.val) := ZMod.nontrivial_iff.mpr (by omega)
  intro h;have hi := congrFun h i;simp [step_apply] at hi

theorem distinct (hn : 1<n.val) (z : Face (Per n)) : Function.Injective (edges z) := by
  have hx:=step_ne hn z.1 z.2.val.1
  have hy:=step_ne hn z.1 z.2.val.2
  have h₀ : z.2.val.1≠z.2.val.2 := z.2.property.ne
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [edges,Prod.mk.injEq]

theorem head_zero (z : Face (Per n)) (U : Config G n) : sideHead z 0 U=faceValue U z := by
  change _=WardBin.wheel (z.1,z.2.val.1) (posDir z.2.val.2) U
  rw [WardBin.wheel_pos];rfl

private theorem word_shift (a : Fin 4 → G.El) (i : Fin 4) (s : G.El) :
    headed (Function.update a i (s*a i)) i=s*headed a i := by
  fin_cases i <;> simp [headed,Function.update,mul_assoc]

theorem shifted (hn : 1<n.val) (z : Face (Per n)) (i : Fin 4) (U : Config G n) (a : G.Color) (t : ℝ) :
    sideHead z i (WardBin.slide (edges z i) U (t•a))=WardBin.left a (sideHead z i U) t := by
  have h (j : Fin 4) : WardBin.slide (edges z i) U (t•a) (edges z j)=
      Function.update (fun j=>U (edges z j)) i (G.lieExp (t•a)*U (edges z i)) j := by
    by_cases hj : j=i
    · subst j;simp [WardBin.slide]
    · have hne : edges z j≠edges z i:=fun h=>(hj (distinct hn z h))
      simp [WardBin.slide,Function.update_of_ne,hj,hne]
  dsimp only [sideHead,WardBin.left]
  simp_rw [h];exact word_shift _ _ _

/-- The native plaquette arclength stays unchanged by a cyclic change of the home bond or reversing the loop. -/
theorem chord (z : Face (Per n)) (i : Fin 4) (U : Config G n) :
    G.chord (sideHead z i U)=G.chord (faceValue U z) := by
  rw [←head_zero]
  let a:=fun k=>U (edges z k)
  change G.chord (headed a i)=G.chord (headed a 0)
  have h₁ : headed a 1=(a 0)⁻¹*headed a 0*((a 0)⁻¹)⁻¹ := by simp [headed,mul_assoc]
  have h₂ : headed a 2=(a 3)⁻¹*(headed a 0)⁻¹*((a 3)⁻¹)⁻¹ := by simp [headed,mul_assoc]
  have h₃ : headed a 3=(headed a 0)⁻¹ := by simp [headed,mul_assoc]
  fin_cases i
  · rfl
  · change G.chord (headed a 1)=G.chord (headed a 0)
    rw [h₁,G.chord_conj]
  · change G.chord (headed a 2)=G.chord (headed a 0)
    rw [h₂,G.chord_conj,G.chord_inv]
  · change G.chord (headed a 3)=G.chord (headed a 0)
    rw [h₃,G.chord_inv]

def startFrame (z : Face (Per n)) (U : Config G n) : Fin 4 → G.El :=
  ![1,(U (edges z 0))⁻¹,(U (edges z 3))⁻¹,1]

/-- All four selected signed physical fields really are the original curvature transported to the observed bond. -/
theorem original (z : Face (Per n)) (i : Fin 4) (U : Config G n) :
    sign i • G.curvature (sideHead z i U)=G.adjoint (startFrame z U i) (G.curvature (faceValue U z)) := by
  rw [←head_zero]
  let a:=fun k=>U (edges z k)
  have h₁ : headed a 1=(a 0)⁻¹*headed a 0*((a 0)⁻¹)⁻¹ := by simp [headed,mul_assoc]
  have h₂ : headed a 2=(a 3)⁻¹*(headed a 0)⁻¹*((a 3)⁻¹)⁻¹ := by simp [headed,mul_assoc]
  have h₃ : headed a 3=(headed a 0)⁻¹ := by simp [headed,mul_assoc]
  change sign i • G.curvature (headed a i)=G.adjoint (startFrame z U i) (G.curvature (headed a 0))
  fin_cases i
  · simp [sign,startFrame]
  · change sign 1 • G.curvature (headed a 1)=G.adjoint (startFrame z U 1) (G.curvature (headed a 0))
    rw [h₁,G.curvature_conjugate];simp [sign,startFrame,a]
  · change sign 2 • G.curvature (headed a 2)=G.adjoint (startFrame z U 2) (G.curvature (headed a 0))
    rw [h₂,G.curvature_conjugate,G.curvature_inv,map_neg];simp [sign,startFrame,a]
  · change sign 3 • G.curvature (headed a 3)=G.adjoint (startFrame z U 3) (G.curvature (headed a 0))
    rw [h₃,G.curvature_inv];simp [sign,startFrame]

theorem c_head (z : Face (Per n)) (i : Fin 4) : Continuous (@sideHead n G z i) := by
  change Continuous (fun U : Config G n=>headed (fun k=>U (edges z k)) i)
  fin_cases i
  · change Continuous (fun U : Config G n=>(U (edges z 0))*(U (edges z 1))*(U (edges z 2))⁻¹*(U (edges z 3))⁻¹);fun_prop
  · change Continuous (fun U : Config G n=>(U (edges z 1))*(U (edges z 2))⁻¹*(U (edges z 3))⁻¹*(U (edges z 0)));fun_prop
  · change Continuous (fun U : Config G n=>(U (edges z 2))*(U (edges z 1))⁻¹*(U (edges z 0))⁻¹*(U (edges z 3)));fun_prop
  · change Continuous (fun U : Config G n=>(U (edges z 3))*(U (edges z 2))*(U (edges z 1))⁻¹*(U (edges z 0))⁻¹);fun_prop

private def orth (i : Axis) : Axis := if i=0 then 1 else 0
private theorem orth_ne (i : Axis) : orth i≠i := by
  by_cases h : i=0
  · simp [orth,h]
  · simpa only [orth,if_neg h] using Ne.symm h

/-- The genuine three-link substitution joins the very same endpoints with no use of e. -/
def detour (e : Edge (Site n)) (U : Config G n) : G.El :=
  U (e.1,orth e.2)*U (e.1+step (orth e.2),e.2)*(U (e.1+step e.2,orth e.2))⁻¹

def bypass (e : Edge (Site n)) (U : Config G n) := Function.update U e (detour e U)

theorem bypass_held (hn : 1<n.val) (e : Edge (Site n)) (U : Config G n) (a : G.Color) :
    bypass e (WardBin.slide e U a)=bypass e U := by
  have h₀ : (e.1,orth e.2)≠e := by intro h;exact orth_ne _ (congrArg Prod.snd h)
  have h₁ : (e.1+step (orth e.2),e.2)≠e := by intro h;exact step_ne hn _ _ (congrArg Prod.fst h)
  have h₂ : (e.1+step e.2,orth e.2)≠e := by intro h;exact orth_ne _ (congrArg Prod.snd h)
  have h : detour e (WardBin.slide e U a)=detour e U := by
    simp [detour,WardBin.slide,Function.update_of_ne,h₀,h₁,h₂]
  funext b;by_cases hb : b=e
  · subst b;simp [bypass,h]
  · simp [bypass,WardBin.slide,Function.update_of_ne hb]

theorem bypass_gauge (e : Edge (Site n)) (U : Config G n) (T : Site n → G.El) :
    bypass e (Lattice.gauge T U)=Lattice.gauge T (bypass e U) := by
  have h : e.1+step (orth e.2)+step e.2=e.1+step e.2+step (orth e.2) := by abel
  funext b;by_cases hb : b=e
  · subst b;simp [bypass,detour,Lattice.gauge,h,mul_assoc]
  · simp [bypass,Lattice.gauge,Function.update_of_ne hb]

/-- The transporter is an original product of physical links with every use of the varied bond replaced by its actual three-link detour. -/
def path (e : Edge (Site n)) (z : Face (Per n)) := route (lift e.1) (lift z.1) 1

theorem stop_path (e : Edge (Site n)) (z : Face (Per n)) : stop e.1 (path e z)=z.1 := by
  calc
    stop e.1 (path e z)=stop (wrap n (lift e.1)) (path e z) := by rw [wrap_lift]
    _=wrap n (stop (lift e.1) (path e z)) := (wrap_stop_cover ..).symm
    _=z.1 := by rw [path,route_end,wrap_lift]

def off (z : Face (Per n)) (e : Edge (Site n)) (U : Config G n) : G.Color :=
  G.adjoint (travel (bypass e U) e.1 (path e z)) (G.curvature (faceValue U z))

theorem off_held (hn : 1<n.val) (z : Face (Per n)) (e : Edge (Site n)) (he : ∀ i:Fin 4,edges z i≠e)
    (U : Config G n) (a : G.Color) : off z e (WardBin.slide e U a)=off z e U := by
  have h (j : Fin 4) : WardBin.slide e U a (edges z j)=U (edges z j) := by simp [WardBin.slide,Function.update_of_ne (he j)]
  simp only [off,bypass_held hn,←head_zero,sideHead,h]

theorem off_gauge (z : Face (Per n)) (e : Edge (Site n)) (U : Config G n) (T : Site n → G.El) :
    off z e (Lattice.gauge T U)=G.adjoint (T e.1) (off z e U) := by
  rw [off,bypass_gauge,Lattice.travel_gauge,stop_path,face_gauge,G.curvature_conjugate,off]
  have cancel (x : G.Color) : G.adjoint (T z.1)⁻¹ (G.adjoint (T z.1) x)=x := by rw [←G.adjoint_mul,inv_mul_cancel,G.adjoint_one]
  simp only [G.adjoint_mul,cancel]

theorem continuous_off (z : Face (Per n)) (e : Edge (Site n)) : Continuous (@off n G z e) := by
  have c : Continuous (bypass e : Config G n → Config G n) := by
    apply continuous_pi;intro b;by_cases hb : b=e
    · subst b;simp [bypass,detour];fun_prop
    · simp [bypass,Function.update_of_ne hb];fun_prop
  let g := fun U : Config G n=>travel (bypass e U) e.1 (path e z)
  have hg : Continuous g := (show Continuous (fun U : Config G n=>travel U e.1 (path e z)) by fun_prop).comp c
  have hf : Continuous (fun U : Config G n=>faceValue U z) := by unfold faceValue;fun_prop
  have eq : off z e=(fun U : Config G n=>G.curvature (g U*faceValue U z*(g U)⁻¹)) := by
    funext U;exact (G.curvature_conjugate _ _).symm
  rw [eq];exact G.continuous_curvature.comp ((hg.mul hf).mul hg.inv)

end YM.Integration.WilsonPlaquetteIncidence
end


/-! The exact original Ward comparison of any signed flow covector, plus each authentic rotated plaquette row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegulatorWardRow
open Filter Set Function MeasureTheory Lattice Wilson RG OPE.Therm Push.GridApprox WilsonPlaquetteWardTrace WilsonPlaquetteIncidence
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def row (L : Form G) (z : Face (Per n)) (i : Fin 4) (U : Config G n) : WardBin.Covector G :=
  L (G.curvature (sideHead z i U))

def measured (L : Form G) (z : Face (Per n)) (i : Fin 4) (U : Config G n) : ℂ :=
  ∑ a : G.ColorIndex,L (differential (WardBin.dirs G a) (sideHead z i U)) (WardBin.dirs G a)

private theorem derivative (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (i : Fin 4) (a : G.Color) (U : Config G n) :
    HasDerivAt (fun t : ℝ=>row L z i (WardBin.slide (edges z i) U (t•a)) a)
      (L (differential a (sideHead z i U)) a) 0 := by
  simp only [row,WilsonPlaquetteIncidence.shifted hn]
  exact (L.flip a).hasFDerivAt.comp_hasDerivAt 0 (based a (sideHead z i U))

theorem flow (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (i : Fin 4) (a : G.ColorIndex) :
    WardBin.HasFlow (edges z i) (WardBin.dirs G a) fun U=>row L z i U (WardBin.dirs G a) := by
  let t:=WardBin.dirs G a
  have slope (U) : WardBin.slope (edges z i) t (fun V=>row L z i V t) U=
      L (differential t (sideHead z i U)) t := (derivative hn L z i t U).deriv
  refine ⟨WardBin.envelope_continuous ((L.flip t).continuous.comp (G.continuous_curvature.comp (c_head z i))),?_,
    fun U=>(derivative hn L z i t U).differentiableAt⟩
  have eq : WardBin.slope (edges z i) t (fun V=>row L z i V t)=(fun U=>L (differential t (sideHead z i U)) t) := funext slope
  rw [eq]
  apply WardBin.envelope_continuous
  apply (L.flip t).continuous.comp
  exact (G.projectColor.continuous_of_finiteDimensional.comp (continuous_const.mul G.continuous_mat)).comp (c_head z i)

theorem price (L : Form G) (z : Face (Per n)) (i : Fin 4) (U : Config G n) :
    ‖measured L z i U-trace L‖≤rate L*G.chord (faceValue U z) := by
  rw [←WilsonPlaquetteIncidence.chord z i U]
  let u:=sideHead z i U
  have h (a : G.ColorIndex) : ‖L (differential (WardBin.dirs G a) u) (WardBin.dirs G a)-L (WardBin.dirs G a) (WardBin.dirs G a)‖≤
      ‖L‖*G.colorScale*G.chord u := by
    rw [←sub_apply,←map_sub]
    apply ((L _).le_opNorm _).trans
    rw [OrthonormalBasis.norm_eq_one,mul_one]
    apply (L.le_opNorm _).trans
    simpa only [OrthonormalBasis.norm_eq_one,mul_one,mul_assoc] using
      mul_le_mul_of_nonneg_left (WilsonPlaquetteWardTrace.chord (WardBin.dirs G a) u) (norm_nonneg L)
  unfold measured trace;rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  exact (Finset.sum_le_sum (fun a _=>h a)).trans_eq (by simp [rate,nsmul_eq_mul];ring)

theorem divergence (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (i : Fin 4) (U : Config G n) :
    WardBin.divergence (edges z i) (row L z i) U=measured L z i U :=
  Finset.sum_congr rfl fun a _=>(derivative hn L z i (WardBin.dirs G a) U).deriv

theorem off_flow (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (e : Edge (Site n)) (he : ∀ i:Fin 4,edges z i≠e)
    (a : G.ColorIndex) : WardBin.HasFlow e (WardBin.dirs G a) fun U=>L (off z e U) (WardBin.dirs G a) := by
  let t:=WardBin.dirs G a
  have eq (U : Config G n) : (fun s : ℝ=>L (off z e (WardBin.slide e U (s•t))) t)=fun _=>L (off z e U) t := by
    funext s;rw [off_held hn z e he]
  refine ⟨WardBin.envelope_continuous ((L.flip t).continuous.comp (continuous_off z e)),?_,?_⟩
  · have zero : WardBin.slope e t (fun U=>L (off z e U) t)=0 := by
      funext U;unfold WardBin.slope;rw [eq];exact deriv_const ..
    rw [zero];exact Envelope.constC 0
  · intro U;rw [eq];exact differentiableAt_const _

theorem off_div (hn : 1<n.val) (L : Form G) (z : Face (Per n)) (e : Edge (Site n))
    (he : ∀ i:Fin 4,edges z i≠e) (U : Config G n) :
    WardBin.divergence e (fun V=>L (off z e V)) U=0 := by
  unfold WardBin.divergence WardBin.slope;simp_rw [off_held hn z e he];simp

variable (C : Family G) (hC : C.Makes) {N p j : ℕ}
local notation "nf" => C.side N p
local notation "β" => C.beta N p
local notation "μ" => scene C.path N p N
include hC

/-- The true Ward identity tested on the complete exterior likelihood of the original trajectory. -/
theorem replace (q : j≤N) {X : Set (Site (C.side j p))} {ζ : Config G (C.side j p) → ℂ}
    (hζ : Envelope ζ) (hX : LocalOn X ζ) (e : Edge (Site nf)) (away : e.1∉WilsonExteriorWardEquations.region C p q X)
    (A : Config G nf → WardBin.Covector G) (hA : ∀ i,WardBin.HasFlow e (WardBin.dirs G i) fun U=>A U (WardBin.dirs G i))
    (c : ℂ) : (∫ W, actualTransport C (N:=N) (fun U=>(β:ℂ)*A U (WardBin.euler U e)-c) q W*ζ W ∂scene C.path N p j)=
      ∫U,(WardBin.divergence e A U-c)*backTo C.path N p q ζ U ∂μ := by
  let E:=WardBin.equation β e A
  let D := fun U=>WardBin.divergence e A U-c
  let B:=backTo C.path N p q ζ
  have hb : (β:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (WardBin.rated hC p N).1.ne'
  have hE : Envelope E := WardBin.equation_bounded hA _
  have hD : Envelope D := (WardBin.envelope_sums _ _ (fun i _=>(hA i).2.1)).subC (Envelope.constC c)
  have hB : Envelope B := backTo_env C.path N p q hζ
  have hid : (fun U=>(β:ℂ)*A U (WardBin.euler U e)-c)=(fun U=>(β:ℂ)*E U+D U) := by
    funext U;dsimp [D,E,WardBin.equation];field_simp [hb];ring
  rw [hid,WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ ((Envelope.constC (β:ℂ)).mulC hE|>.addC hD)]
  have null := WilsonExteriorWardEquations.original C p hC q hζ hX e away A hA
  rw [WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ hE] at null
  letI : IsProbabilityMeasure μ := probability (H:=C.path) (p:=p) hC.wilson le_rfl
  change (∫U,((β:ℂ)*E U+D U)*B U ∂μ)=∫U,D U*B U ∂μ
  simp_rw [add_mul,mul_assoc]
  rw [integral_add (((hE.mulC hB).integrableC _).const_mul _) ((hD.mulC hB).integrableC _),integral_const_mul]
  change (∫U,E U*B U ∂μ)=0 at null;rw [null,mul_zero,zero_add]

end YM.Integration.WilsonRegulatorWardRow
end


/-! A whole physical combined bond vector. Its measured finite error costs only the four genuinely incident coefficients, even if the original vector has full support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWeightedPlaquetteResponse
open Filter Set MeasureTheory Lattice Wilson RG OPE.Therm Push.GridApprox WilsonPlaquetteWardTrace WilsonPlaquetteIncidence
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

abbrev Other (z : Face (Per n)) := {e : Edge (Site n) // ∀ i:Fin 4,edges z i≠e}

def cost (z : Face (Per n)) (v : Edge (Site n) → ℝ) := ∑ i:Fin 4,|v (edges z i)|

theorem unit_cost (hn : 1<n.val) (z : Face (Per n)) (v : Edge (Site n) → ℝ)
    (hw : ∑ e,(v e)^2≤1) : cost z v≤2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 4=>(1:ℝ)) (fun i=>|v (edges z i)|)
  have hi : (∑ i : Fin 4,(v (edges z i))^2)≤1 := by
    let A:=Finset.univ.image (edges z)
    have ha : ∑ e∈A,(v e)^2=∑ i : Fin 4,(v (edges z i))^2 :=
      Finset.sum_image (fun i _ j _ hij=>distinct hn z hij)
    rw [←ha];exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _=>sq_nonneg _)).trans hw
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one,sq_abs] at h
  unfold cost;nlinarith

def model (L : Form G) (z : Face (Per n)) (v : Edge (Site n) → ℝ) (U : Config G n) : ℂ :=
  (∑ i : Fin 4, ((sign i*v (edges z i):ℝ):ℂ)*WilsonRegulatorWardRow.row L z i U (WardBin.euler U (edges z i)))+
  ∑ e : Other z, (v e.val:ℂ)*L (off z e.val U) (WardBin.euler U e.val)

def deviation (L : Form G) (z : Face (Per n)) (v : Edge (Site n) → ℝ) (U : Config G n) : ℂ :=
  ∑ i : Fin 4, ((sign i*v (edges z i):ℝ):ℂ)*(WilsonRegulatorWardRow.measured L z i U-trace L)

private theorem abs_sign (i : Fin 4) : |sign i|=1 := by fin_cases i <;> norm_num [sign]

theorem point (L : Form G) (z : Face (Per n)) (v : Edge (Site n) → ℝ) (U : Config G n) :
    ‖deviation L z v U‖≤cost z v*rate L*G.chord (faceValue U z) := by
  unfold deviation cost
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum;intro i _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_sign,one_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (WilsonRegulatorWardRow.price L z i U) (abs_nonneg _)

private theorem bounded (L : Form G) {F H : Config G n → G.Color} (hf : Continuous F) (hh : Continuous H) :
    Envelope (fun U=>L (F U) (H U)) := WardBin.envelope_continuous ((L.continuous.comp hf).clm_apply hh)

theorem model_env (L : Form G) (z : Face (Per n)) (v : Edge (Site n) → ℝ) : Envelope (model L z v) := by
  apply Envelope.addC
  · apply WardBin.envelope_sums
    intro i _;exact (Envelope.constC _).mulC (bounded L (G.continuous_curvature.comp (c_head z i)) WardBin.continuous_euler)
  · apply WardBin.envelope_sums
    intro e _;exact (Envelope.constC _).mulC (bounded L (continuous_off z e.val) WardBin.continuous_euler)

private theorem muSum {ι : Type*} [Fintype ι] (μ : Measure (Config G n)) [IsFiniteMeasure μ]
    (a : ι → ℂ) (f : ι → Config G n → ℂ) (h : ∀ i,Envelope (f i)) :
    (∫ U, ∑ i,a i*f i U ∂μ)=∑ i,a i*(∫ U,f i U ∂μ) := by
  rw [integral_finsetSum _ (fun i _=>(h i|>.integrableC μ).const_mul _)];simp_rw [integral_const_mul]

variable (C : Family G) (hC : C.Makes) {N p j : ℕ}
local notation "nf" => C.side N p
local notation "β" => C.beta N p
local notation "μ" => scene C.path N p N
include hC

/-- Exact all-volume strong coupling-free reduction of the original signed Euler-curl weighted current to its four true microscopic derivative rows. -/
theorem residual (q : j≤N) {X : Set (Site (C.side j p))} {ζ : Config G (C.side j p) → ℂ}
    (hζ : Envelope ζ) (hX : LocalOn X ζ) (L : Form G) (z : Face (Per nf)) (v : Edge (Site nf) → ℝ)
    (away : ∀ e,v e≠0 → e.1∉WilsonExteriorWardEquations.region C p q X) :
    (∫ W, actualTransport C (N:=N) (fun U=>(β:ℂ)*model L z v U-(curl z v:ℂ)*trace L) q W*ζ W ∂scene C.path N p j)=
      ∫U,deviation L z v U*backTo C.path N p q ζ U ∂μ := by
  letI : IsProbabilityMeasure μ:=probability (H:=C.path) (p:=p) hC.wilson le_rfl
  let B:=backTo C.path N p q ζ
  let hB : Envelope B:=backTo_env C.path N p q hζ
  let hn : 1<(C.side N p).val := lt_of_lt_of_le (by decide : 1<4) (Next.Foundations.actual_side_ge C.S N p)
  let b (i : Fin 4) : ℂ := (sign i*v (edges z i):ℝ)
  let A (i : Fin 4) := WilsonRegulatorWardRow.row L z i
  let O (e : Other z) (U : Config G nf) := L (off z e.val U)
  let E (i : Fin 4) (U : Config G nf) := (β:ℂ)*A i U (WardBin.euler U (edges z i))-trace L
  let H (e : Other z) (U : Config G nf) := (β:ℂ)*O e U (WardBin.euler U e.val)
  let D (i : Fin 4) (U : Config G nf):=WilsonRegulatorWardRow.measured L z i U-trace L
  have envE (i) : Envelope (E i) := ((Envelope.constC (β:ℂ)).mulC
    (bounded L (G.continuous_curvature.comp (c_head z i)) WardBin.continuous_euler)).subC (Envelope.constC _)
  have envH (e) : Envelope (H e) := (Envelope.constC (β:ℂ)).mulC (bounded L (continuous_off z e.val) WardBin.continuous_euler)
  have envD (i) : Envelope (D i) := by
    have H := WardBin.envelope_sums Finset.univ _ (fun a _=>(WilsonRegulatorWardRow.flow hn L z i a).2.1)
    have e : WardBin.divergence (edges z i) (A i)=WilsonRegulatorWardRow.measured L z i := funext (WilsonRegulatorWardRow.divergence hn L z i)
    change Envelope (WardBin.divergence (edges z i) (A i)) at H;rw [e] at H;exact H.subC (Envelope.constC _)
  have eI (i) : b i*(∫ U,E i U*B U ∂μ)=b i*(∫ U,D i U*B U ∂μ) := by
    by_cases h : v (edges z i)=0
    · simp [b,h]
    · have hz:=WilsonRegulatorWardRow.replace C hC q hζ hX (edges z i) (away _ h) (A i)
          (WilsonRegulatorWardRow.flow hn L z i) (trace L)
      rw [WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ (envE i)] at hz
      change (∫U,E i U*B U ∂μ)=∫U,(WardBin.divergence (edges z i) (WilsonRegulatorWardRow.row L z i) U-trace L)*B U ∂μ at hz
      simp_rw [WilsonRegulatorWardRow.divergence hn L z i] at hz
      exact congrArg (b i*·) hz
  have eH (e : Other z) : (v e.val:ℂ)*(∫ U,H e U*B U ∂μ)=0 := by
    by_cases h : v e.val=0
    · simp [h]
    · have hz:=WilsonRegulatorWardRow.replace C hC q hζ hX e.val (away _ h) (O e)
          (WilsonRegulatorWardRow.off_flow hn L z e.val e.property) 0
      simp only [sub_zero] at hz
      rw [WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ (envH e)] at hz
      change (∫U,H e U*B U ∂μ)=∫U,WardBin.divergence e.val (fun U=>L (off z e.val U)) U*B U ∂μ at hz
      simp only [WilsonRegulatorWardRow.off_div hn L z e.val e.property,zero_mul,integral_zero] at hz
      rw [hz,mul_zero]
  have cc : (curl z v:ℂ)=∑ i,b i := by simp [curl,b,Complex.ofReal_sum]
  have mix (U : Config G nf) : ((β:ℂ)*model L z v U-(curl z v:ℂ)*trace L)*B U=
      (∑ i,b i*(E i U*B U))+(∑ e : Other z,(v e.val:ℂ)*(H e U*B U)) := by
    rw [cc];unfold model E H;dsimp only [b,A,O]
    simp only [mul_add,add_mul,sub_mul,mul_sub,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]
    simp only [mul_left_comm (β:ℂ),mul_assoc];ring
  have endrow (U : Config G nf) : deviation L z v U*B U=∑ i,b i*(D i U*B U) := by
    unfold deviation;rw [Finset.sum_mul];simp only [b,D,mul_assoc]
  rw [WilsonExteriorWardEquations.adjoint C p hC hζ q le_rfl _ (((Envelope.constC (β:ℂ)).mulC (model_env L z v)).subC (Envelope.constC _))]
  change (∫U,((β:ℂ)*model L z v U-(curl z v:ℂ)*trace L)*B U ∂μ)=∫U,deviation L z v U*B U ∂μ
  simp_rw [mix,endrow]
  have Bi (i) := (envE i).mulC hB
  have Bo (e) := (envH e).mulC hB
  have Bd (i) := (envD i).mulC hB
  rw [integral_add ((WardBin.envelope_sums _ _ (fun i _=>(Envelope.constC _).mulC (Bi i))).integrableC μ)
    ((WardBin.envelope_sums _ _ (fun e _=>(Envelope.constC _).mulC (Bo e))).integrableC μ),muSum μ b _ Bi,
    muSum μ (fun e : Other z=>(v e.val:ℂ)) _ Bo,muSum μ b _ Bd]
  simp_rw [eI,eH];simp

/-- One cutoff for every period, weighted original bond vector and measured exterior; only four genuine incident entries pay. -/
theorem original (P : Poetry C.path.levels) (hG : G.Simple) {s : ℝ} (hs : s<1) :
    ∀ᶠ N : ℕ in atTop, ∀ p j (q : j≤N) (L : Form G) (z : Face (Per (C.side N p))) (v : Edge (Site (C.side N p)) → ℝ)
      (X : Set (Site (C.side j p))) (ζ : Config G (C.side j p) → ℂ), Measurable ζ → (∀ W,‖ζ W‖≤1) → LocalOn X ζ → 
      (∀ e,v e≠0 → e.1∉WilsonExteriorWardEquations.region C p q X) → 
    ‖∫ W,actualTransport C (N:=N) (fun U=>(C.beta N p:ℂ)*model L z v U-(curl z v:ℂ)*trace L) q W*ζ W ∂scene C.path N p j‖≤
        3*cost z v*rate L*(C.path.levels.clock.hatCoupling N)^s := by
  filter_upwards [rare P hG hC.wilson,WilsonCurvatureRankRate.thermal C.path.levels hG 1 (s:=s) (by simpa only [Nat.cast_one] using hs)] with N hr h
  intro p j q L z v X ζ hm h1 hx away
  rw [residual C hC q ⟨hm,1,h1⟩ hx L z v away]
  letI : IsProbabilityMeasure (scene C.path N p N):=probability (H:=C.path) (p:=p) hC.wilson le_rfl
  let D (U : Config G (C.side N p)):=deviation L z v U*backTo C.path N p q ζ U
  have hd (U) : ‖D U‖≤(cost z v*rate L)*(G.chord (faceValue U z))^1 := by
    rw [pow_one];exact (le_of_eq (norm_mul _ _)).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (backTo_bound C.path N p q hm 1 h1 U)).trans (point L z v U))
  have hR : 0≤cost z v*rate L := by unfold cost rate;positivity [G.colorScale_pos]
  apply (norm_integral_le_integral_norm _).trans
  apply (WilsonPlaquetteMoments.weighted _ z 1 h.1 (hr N le_rfl p z) hR _ (fun U=>norm_nonneg _) hd).trans
  have h₁ : cool C.path.levels N≤(C.path.levels.clock.hatCoupling N)^s := by simpa only [pow_one] using h.2.1
  rw [pow_one,pow_one];nlinarith [mul_le_mul_of_nonneg_left h₁ hR,mul_le_mul_of_nonneg_left h.2.2 hR]

end YM.Integration.WilsonWeightedPlaquetteResponse
end


/-! The true Wilson expectation detects the same nonzero microscopic curl for every original side and normalized bond vector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalCurlDetection
open Filter Set MeasureTheory Lattice Wilson RG OPE.Therm WilsonPlaquetteIncidence WilsonPlaquetteWardTrace WilsonWeightedPlaquetteResponse
open scoped Classical BigOperators Topology
variable {G : Gauge}

variable (C : Family G) (hC : C.Makes) (P : Poetry C.path.levels) (hG : G.Simple)

def observed (N p : ℕ) (L : Form G) (z : Face (Per (C.side N p))) (v : Edge (Site (C.side N p)) → ℝ) : ℂ :=
  (C.beta N p:ℂ)*∫U,model L z v U ∂scene C.path N p N

include hC P hG

/-- A side-independent ℓ² unit ball, including vectors with every bond excited. Its measured trace is sensitive to all four orientations. -/
theorem original {s : ℝ} (h : s<1) : ∀ᶠ N : ℕ in atTop, ∀ p (L : Form G)
    (z : Face (Per (C.side N p))) (v : Edge (Site (C.side N p)) → ℝ), (∑e,(v e)^2)≤1 → 
    ‖observed C N p L z v-(curl z v:ℂ)*trace L‖≤6*rate L*(C.path.levels.clock.hatCoupling N)^s := by
  filter_upwards [WilsonWeightedPlaquetteResponse.original C hC P hG h] with N hN
  intro p L z v hv
  haveI : IsProbabilityMeasure (scene C.path N p N) := probability (H:=C.path) (p:=p) hC.wilson le_rfl
  have hn : 1<(C.side N p).val := lt_of_lt_of_le (by decide : 1<4) (Next.Foundations.actual_side_ge C.S N p)
  have hfin:=hN p N le_rfl L z v ∅ (fun _=>1) measurable_const (fun _=>by simp) (fun _ _ _=>rfl)
    (fun _ _=>by simp [WilsonExteriorWardEquations.region,Nat.leRecOn_self])
  rw [actualTransport_base C hC le_rfl] at hfin
  simp only [mul_one] at hfin
  rw [integral_sub ((WilsonWeightedPlaquetteResponse.model_env L z v).integrableC _ |>.const_mul _) (integrable_const _),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hfin
  apply hfin.trans
  have hr : 0≤rate L:=by unfold rate; positivity [G.colorScale_pos]
  have hg : 0≤(C.path.levels.clock.hatCoupling N)^s:=Real.rpow_nonneg (inv_pos.mpr (Real.sqrt_pos.mpr
    (zero_lt_one.trans (C.path.levels.fits.delayed N)))).le _
  have hc:=unit_cost hn z v hv;gcongr;nlinarith

omit hC P hG in
private theorem dim (simple : G.Simple) : 0<(Fintype.card G.ColorIndex:ℝ) := by
  haveI : Nonempty G.ColorIndex := by
    by_contra! he;haveI : IsEmpty G.ColorIndex:=he
    haveI:=Gauge.Simple.nontrivial_color simple;obtain ⟨a,b,hab⟩:=exists_pair_ne G.Color
    exact hab (by ext i;exact isEmptyElim i)
  exact_mod_cast Fintype.card_pos

/-- Every normalized actual free direction retaining at least one-third of one oriented curl has a strictly nonzero Wilson contraction, with a cutoff uniform in the torus. -/
theorem positive : ∀ᶠ N : ℕ in atTop, ∀ p (z : Face (Per (C.side N p)))
    (v : Edge (Site (C.side N p)) → ℝ), (∑e,(v e)^2)≤1 → 1/3≤|curl z v| → 
    (Fintype.card G.ColorIndex:ℝ)/6 < ‖observed C N p (WilsonWardMetric.metric G) z v‖ := by
  let L:=WilsonWardMetric.metric G
  let d : ℝ:=Fintype.card G.ColorIndex
  have hd : 0<d:=dim hG
  have hq := (Multi.Wage.small_hat hG C.path.levels).rpow_const (p:=(1/2:ℝ)) (Or.inr (by norm_num : 0≤(1/2:ℝ)))
  have hs : Tendsto (fun N=>6*rate L*(C.path.levels.clock.hatCoupling N)^(1/2:ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1/2:ℝ)≠0),mul_zero] using (tendsto_const_nhds (x:=6*rate L)).mul hq
  filter_upwards [original C hC P hG (s:=(1/2:ℝ)) (by norm_num),hs.eventually (gt_mem_nhds (by positivity : 0<d/6))] with N hn hε
  intro p z v hv hz
  let a:=observed C N p L z v
  have he:=hn p L z v hv
  change ‖a-(curl z v:ℂ)*trace L‖≤_ at he
  have ht : ‖(curl z v:ℂ)*trace L‖=|curl z v| *d := by
    simp [L,WilsonWardMetric.metric_trace,d,Real.norm_eq_abs]
  have tri := norm_sub_le (a-(curl z v:ℂ)*trace L) a
  have eqn : a-(curl z v:ℂ)*trace L-a= -((curl z v:ℂ)*trace L) := by ring
  rw [eqn,norm_neg,ht] at tri
  have hlow : d*(1/3)≤|curl z v| *d := by rw [mul_comm];exact mul_le_mul_of_nonneg_right hz hd.le
  change d/6 < ‖a‖;linarith

end YM.Integration.WilsonPhysicalCurlDetection
end
