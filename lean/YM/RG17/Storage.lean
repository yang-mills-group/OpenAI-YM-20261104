import YM.RG17.Sheared
import YM.Trace2.HeatGrowth

/-!
Centering. Don't simply drop constant moments. Get tested
r^8τ² full trace laws under the same pending Ward coefficients.
These are at true continuum labels on the advertised UV path.
Next: anti-monotonicity and enough offset control via phase
(OPE Services) to recover point `LogLaw` on this F.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Set Function Filter MeasureTheory Table Spec Extraction OPE OPE.Orbits
open Points Analysis Work.A05 Trace
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} {F:Final C f S} {L:Layout F}

-- monotonicity argument must use positive selected phase not inferred from off-shell euclidean choices!
def span2 (x:Points 2) := ‖x 1-x 0‖
def freeCharge (C:Family G) (t:ℝ):= theoryDensity G/t^8
abbrev modCharge (C:Family G)(x:Points 2):ℂ:= freeCharge C (span2 x)
def discount (r:ℝ):= r^8* OPE.run r^2
lemma discount_eq (r:ℝ) : discount r=logWeight r⁻¹:= by rw [discount,logWeight,inv_inv,OPE.run,Real.log_inv]
lemma spanPos {x:Points 2}(h:x∈conf _):0<span2 x:=norm_sub_pos_iff.mpr (h.ne (by decide : (1:Fin 2) ≠0))
lemma span_sc {r:ℝ} (x:Points 2) (h:0<r):span2 (r•x)=r*span2 x := by change ‖r•_ - r•(x 0)‖ = _; rw [← smul_sub,norm_smul, Real.norm_of_nonneg h.le]; rfl
lemma span_cont : Continuous span2:=by unfold span2; fun_prop
lemma freeCharged (ψ:Test 2) : plate (S:=Maxwell.freeTable C.labels) (d:=fun _=>4) (![φS C,φS C]) 1 ψ=ψ.applyTo (modCharge C):=by
    rw [pair_plate]; refine ψ.apply_eq fun x hx=> ?_; rw [one_smul]; unfold modCharge freeCharge span2
    rw [norm_sub_rev]; refine Eq.trans ?_ (Trace.free_expression x (C:=C) hx); unfold bilim; rw [show Fin.cons _ _=scalarCompar (C:=C) from ?_]; rfl
    ext1 i; fin_cases i <;> rfl
private lemma meanHere {B:Register G}{S:Table B} (v:S.Field 4) (T:Test 1) (r:ℝ) (h:S.Hierarchy): plate (d:=fun _=>4) ![v] r T = (∫ x:Points 1,T x)*first_value 4 v:=by
    rw [← integral_mul_const]; apply integral_congr_ae; filter_upwards with x
    apply congr_arg (T x * ·); unfold first_value
    let y:= r•x
    have he: y=Points.across (y 0) 0:= PiLp.ext (fun i=>by fin_cases i; change _=0+y 0; simp)
    change S.useAt S y _=_
    nth_rw 1 [he]; rw [show tags (d:=fun _=>4) ![v]=fun _:Fin 1=>⟨4,v⟩ from funext (fun i=>by fin_cases i;rfl)]
    exact h.translations 1 (0:Points 1) (valid_one _) (y 0) (fun _=>⟨4,S.representative 4 v⟩)
lemma meanProbe : ∃ T:Test 1,(∫ x:Points 1,T x) ≠ 0:=by
    by_contra! h
    have hh (T:Test 1):T.applyTo (fun _=>(1:ℂ))=0 :=by simpa only [Test.applyTo,mul_one] using h T
    have he:= Test.weak_null (K:=fun _ : Points 1=> (1:ℂ)) continuousOn_const|>.1 hh (show (0:Points 1)∈conf 1 from valid_one _)
    exact one_ne_zero he
variable (Z:Ledger L) (A:Ports C) (H:Services C f S) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (loc:Located L) (V:Tide Z A) (Q:Passage Z A)
include P H loc V Q A Z
set_option quotPrecheck false
local notation "P!"=> portal L
local notation "M!"=> Maxwell.freeTable C.labels
private lemma meanAcross : Tendsto (fun r=> first_value 4 (scalarRay P! r)) home (𝓝 0):=by
    obtain ⟨T,hT⟩:=meanProbe
    let x:= ∫ z:Points 1,T z
    have hv:= wave_zero Z A H P loc V Q (![φS C]) (by decide) T
    have hh: plate (S:=M!) (d:=fun _=>4) ![φS C] 1 T = 0:=by
        -- first_value generic; generalize meanHere (it is C-book?)
        rw [meanHere _ T 1 (Maxwell.Free.hierarchy C.labels), Trace.mean_scalar_free,mul_zero]
    rw [hh] at hv
    have hh:=hv.div_const x; rw [zero_div] at hh; refine hh.congr fun r=> ?_
    rw [show (fun i=> P! r (![φS C] i))=![scalarRay P! r] from funext (fun i=>by fin_cases i; rfl)]
    rw [meanHere _ T r F.room.kernel,mul_comm]; exact mul_div_cancel_right₀ _ hT

lemma planeData (ψ:Test 2): Tendsto (fun r=> plate (d:=fun _=>4) ![focus (C:=C) 4 (scalarRay P! r),focus (C:=C) 4 (scalarRay P! r)] r ψ) home (𝓝 (ψ.applyTo (modCharge C))):=by
    let v r:=scalarRay P! r; let x:=∫ z:Points 2,ψ z
    have hp:= meanAcross Z A H P loc V Q; have hc:= wave_zero Z A H P loc V Q (![φS C,φS C]) (by decide) ψ; rw [freeCharged] at hc
    have he:=hc.sub ((hp.pow 2).const_mul x); rw [zero_pow (by decide : 2≠0),mul_zero,sub_zero] at he; apply he.congr'; filter_upwards [positiveLength] with r hr
    rw [show (fun i=> P! r (![φS C,φS C] i)) = ![v r, v r] from funext (fun i=>by fin_cases i <;> rfl)]
    -- replace explicitly
    rw [pair_plate, pair_plate]; let u (z:Points 2):= custom (r • z) (v r) (v r)
    have hp:EqOn (fun y:Points 2=>custom (r•y) (focus (C:=C) 4 (v r)) (focus (C:=C) 4 (v r))) (fun y=> u y-(first_value 4 (v r))^2) (conf _) := fun y hy=> focus_read F.room.kernel _ (smul_conf hr hy)
    change ψ.applyTo u - x* _=ψ.applyTo (fun y: Points 2=> custom (r•y) (focus (C:=C) 4 (v r)) (focus (C:=C) 4 (v r)))
    rw [ψ.apply_eq hp]; unfold x Test.applyTo; simp_rw [mul_sub]; rw [MeasureTheory.integral_sub (ψ.smearing (show ContinuousOn u (conf 2) from (dualSmooth (v r) (v r) hr F.room.kernel|>.continuousOn))) ((ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).mul_const _), integral_mul_const]
    try rfl

omit P loc V Q H Z A
lemma weighted (hG:G.Simple): G.slopeConstant = 2*anomalyCoefficient G:=by unfold Gauge.slopeConstant anomalyCoefficient; ring
include P H loc V Q Z A
lemma accumulated (t:Handles L)(ψ:Test 2) : Tendsto (fun r=> ψ.applyTo fun y=> discount r • θDiagram F (r • y)) home (𝓝 (ψ.applyTo (modCharge C))):=by
    obtain ⟨a,d,k,hK,H_a,H_d⟩:= fasteners Z A H P loc V Q t
    let v r:=focus (C:=C) 4 (scalarRay P! r)
    let b:=Trace.anomalyCoefficient G
    have hs:G.slopeConstant=2*b:=weighted Z.simple
    have hh:= (((H_d.const_mul 4).mul Z.contour).pow 2).smul (planeData Z A H P loc V Q ψ)
    rw [hs,show (4*(-(Trace.anomalyCoefficient G/2))*(2*b)⁻¹)^2=(1:ℝ) from ?_, one_smul] at hh
    · refine hh.congr' (hK.mono (fun r hr=>?_))
      rw [pair_plate]
      change _ • (∫ z:Points 2,ψ z*custom (r•z) (v r) (v r)) = ∫ z:Points 2, ψ z * _
      rw [← integral_smul]; apply integral_congr_ae; filter_upwards with y
      change (4*(d r /Z.g r^2)*(Z.g r^2*OPE.run r))^2 • _ =ψ y*(discount r • θDiagram F _)
      have hz (c:ℝ) (h:c≠0) : 4*(d r /c^2)*(c^2*OPE.run r)= OPE.run r *(4*d r):=by field_simp; try ring
      rw [show 4*(d r /Z.g r^2)*(Z.g r^2*OPE.run r)= OPE.run r *(4*d r) from hz _ (Z.positive r).ne']; unfold θDiagram discount; rw [mul_comm (r^8),mul_smul,raw_focus_exact,trace_ray_eval F P! hr]; simp only [Complex.real_smul,mul_pow]; unfold v; push_cast; ring
    have h': b≠0:= (anomalyCoefficient_pos Z.simple).ne'
    change (4*(-(b/2))*(2*b)⁻¹)^2=1; field_simp; ring
end YM.RG17

