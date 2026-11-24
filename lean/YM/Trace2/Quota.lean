import YM.Trace2.Along
import YM.PertExtension.Running

/-! Ward determination on the actual bare-hierarchy measuring sequences.
Only leading Wick comparison under existing receipts; positive-rate use conditional.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Trace
open Function Filter Set Table Spec Analysis Points Maxwell Climb Next.UVStress PertExtension UVNext.FreeStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
open Classical Complex
local notation "E" => freeTable C.labels
local notation "s₀" => scalarLabel C.labels

def leftMetric : (E).Stress := fun i j => if i=j then metric0 C.labels i j else 0
def rightMetric : (E).Stress := fun i j => if i=j then 0 else metric0 C.labels i j

variable (U : Actual C F S)
local notation "A" => U.M.hT.spin
abbrev pullY (k : ℕ) : (E).Stress := fun i j=> (U.curve.U k 4).symm ((U.curve.r k)^4 • U.F.sector.energy i j)
lemma metric_pack : (-(1:ℝ)/2) • coilA C.labels A + ((1:ℝ)/4) • coilB C.labels A + (-(1:ℝ)) • coilC C.labels A=
       -(generator C.labels A):= by
  apply Subtype.ext
  change (-1/2:ℝ) • east C.labels + (1/4:ℝ) • west C.labels + (-1:ℝ) • UVNext.FreeStress.across C.labels = -(((1:ℝ)/2) • east C.labels + (-1/4:ℝ) • west C.labels + (1:ℝ) • UVNext.FreeStress.across C.labels)
  module
lemma pullY_tends (h : G.Simple) : Tendsto (pullY U) atTop (𝓝 (metric0 C.labels)) := tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=> by
    have ht:= U.stress i j
    rw [required 1 h U.M U.free_stress,inv_neg,inv_one, Complex.ofReal_neg, Complex.ofReal_one,U.free_stress,torch,one_smul,neg_one_smul] at ht
    apply ht.congr
    intro k; unfold pullY; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (U.curve.r k^4)]; rfl
lemma pullY_in (k)(hk:Spin.realH U.F.room.kernel.spin A (U.curve.U k 4)): reCenter (E) (pullY U k) ∈ KernelSpace A := by
    let Y:=U.curve.U k 4; let y : S.Stress:= (U.curve.r k)^4 • U.F.sector.energy
    have hy: U.F.sector.energy ∈ SymSpace U.F.room.kernel.spin:= sym_mem.mpr ⟨U.F.phase.transport.conserved.symmetric,U.F.phase.transport.conserved.real,fun s i j => by rw [←U.F.phase.transport.spots.signed]; exact U.F.phase.transport.spin ..⟩
    apply enters U.M.hT
    obtain ⟨hu,ht,hr⟩:= sym_mem.mp ((SymSpace _).smul_mem ((U.curve.r k)^4) hy : y∈SymSpace U.F.room.kernel.spin)
    apply sym_mem.mpr
    refine ⟨fun i j=> congr_arg Y.symm (hu i j),fun i j=>Y.injective (by rw [hk.2,LinearEquiv.apply_symm_apply]; exact ht i j), ?_⟩
    intro s i j
    have hf:= congr_arg Y.symm (hr s i j)
    rw [← LinearEquiv.symm_apply_apply Y ((E).mirror A 4 s _),hk.1,LinearEquiv.apply_symm_apply]
    change Y.symm (S.mirror _ _ _ (y i j))=_
    rw [hf]; simp only [map_sum,map_smul]; rfl
lemma centered_pull (h : G.Simple) : Tendsto (fun k=>reCenter (E) (pullY U k)) atTop
   (𝓝 (metric0 C.labels)) := by
   suffices hz:reCenter (E) (metric0 C.labels)=metric0 C.labels from hz ▸ ((reCenter (E)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (pullY_tends U h))
   rw [show metric0 C.labels = -(canonicalStress C.labels: (E).Stress) from rfl,← lighting C.labels A]
   rw [map_neg]; congr 1; funext i j
   change centering (E) 4 _ = _; rw [value_center, (kernel_mem.mp (generator C.labels A).property).2,zero_smul,sub_zero]

def coordsUn : ((ℝ×ℝ×ℝ) →ₗ[ℝ] (E).Stress) := (Submodule.subtype _).comp (mix C.labels A)
lemma coords_kernel (h:G.Simple) : (coordsUn U).ker=⊥:=by
   apply LinearMap.ker_eq_bot.mpr; exact Subtype.val_injective.comp (mixed_space C.labels A h U.M.T.W U.M.lit.pales U.M.lit.hers).1

def pathFields := fun k=> U.curve.U k 4
def lateral (k : ℕ) (K:(E).Stress)(v:S.Field 4):= ((U.curve.r k) • (∑ i:Axis,customDer (separated (U.curve.r k)) i (U.curve.U k 4 (K i timeAxis)) v))
structure Quota (a b d:ℕ→ℝ)(g:ℕ→Axis→Axis→ℂ) : Prop where
    primaryA : Tendsto a atTop (𝓝 1)
    primaryB : Tendsto b atTop (𝓝 1)
    recessive : Tendsto d atTop (𝓝 0)
    quotes : ∀ᶠ k in atTop, ∀ i j, pullY U k i j = a k • leftMetric (C:=C) i j + b k • rightMetric (C:=C) i j + (if i=j then d k • s₀ else 0) + g k i j • (E).unit 4
    fits : ∀ᶠ k in atTop, U.curve.U k 4 ((E).unit 4) = S.unit 4

lemma painted_path (Z:ℝ×ℝ×ℝ) (J:(E).Stress)(hk:reCenter (E) J=(coordsUn U) Z)
       (i j:Axis): J i j=(2*Z.2.1-Z.1) • leftMetric i j + -Z.2.2 • rightMetric i j + (if i=j then (Z.1+2*Z.2.1) • s₀ else 0) + expectation (E) 4 (J i j) • (E).unit 4 := by
   have hh := congr_fun (congr_fun hk i) j
   change centering (E) 4 (J i j) = Z.1 • east C.labels i j + Z.2.1 • west C.labels i j + Z.2.2 • UVNext.FreeStress.across C.labels i j at hh
   rw [value_center] at hh
   -- avoid rw on J both sides
   apply (sub_eq_iff_eq_add.mp hh).trans
   apply congrArg (· + _)
   obtain rfl|hneq:=eq_or_ne i j
   · have hx:=scalar_actual C.labels;have ht:=total_at C.labels i
     have hv := (show s₀=(4:ℝ)⁻¹ • UVNext.FreeStress.total C.labels from by rw [hx]; module)
     simp only [east,west,splitDiag,UVNext.FreeStress.across,if_true,smul_zero,add_zero,rightMetric,leftMetric,metric0,canonicalStress,hv,ht,near]
     simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; push_cast;module
   · simp [hneq, leftMetric,rightMetric,east,west,splitDiag,UVNext.FreeStress.across,metric0,canonicalStress]
lemma load_path (h:G.Simple) : ∃ a b d g, Quota U a b d g := by
   let A':=coordsUn U
   obtain ⟨L,hL⟩:=LinearMap.exists_leftInverse_of_injective A' (coords_kernel U h)
   let v(k):=L (reCenter (E) (pullY U k))
   let u:ℝ×ℝ×ℝ := (-1/2,1/4,-1)
   have hue: A' u=metric0 C.labels:= by
      unfold metric0;rw [← lighting C.labels A] -- rewrite lhs? lighting not present; RHS hidden
      have he:=metric_pack U;change ((-1/2:ℝ) • coilA C.labels A + _ + _).val= _; exact congr_arg Subtype.val he
   have hm: Tendsto v atTop (𝓝 u):= by
      have ht:= L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (centered_pull U h)
      simp only [← hue] at ht; exact (show L (A' u)=u from LinearMap.congr_fun hL u) ▸ ht
   have hv : ∀ᶠ k in atTop, reCenter (E) (pullY U k)=A' (v k):=by
      filter_upwards [U.aligned.hsym 4] with k hk
      let c:KernelSpace A := ⟨_,pullY_in U k hk⟩
      obtain ⟨x,hx0⟩:=(mixed_space C.labels A h U.M.T.W U.M.lit.pales U.M.lit.hers).2 c
      have hh : (A' x) = _:= congr_arg Subtype.val hx0
      change A' x = (reCenter _ _) at hh; change (reCenter _ _) = _; rw [← hh]; simp only [v,←hh, show L (A' x)=x from LinearMap.congr_fun hL x]
   refine ⟨fun k=>2*(v k).2.1-(v k).1,fun k=>-(v k).2.2,fun k=>(v k).1+2*(v k).2.1,fun k i j=>expectation (E) 4 (pullY U k i j),?_,?_,?_,?_,U.aligned.units 4⟩
   · convert ((hm.snd_nhds.fst_nhds.const_mul 2).sub hm.fst_nhds) using 2; norm_num [u]
   · exact (show -u.2.2=1 by dsimp [u]; ring) ▸ hm.snd_nhds.snd_nhds.neg
   · convert (hm.fst_nhds.add (hm.snd_nhds.fst_nhds.const_mul 2)) using 2; norm_num [u]
   filter_upwards [hv] with k hk i j
   exact painted_path U _ _ hk i j
local notation "x₀" k => separated (U.curve.r k)
local notation "Σr" k => focus (S:=S) 4 (testScalar U.curve k)
namespace Quota
variable {U}{a b d:ℕ→ℝ}{g:ℕ→Axis→Axis→ℂ} (Q:Quota U a b d g)
include Q
lemma terms : ∀ᶠ k in atTop, let r:=U.curve.r k; r • (∑ i:Axis,customDer (x₀ k) i (r^4 • U.F.sector.energy i timeAxis) (Σr k)) =
     a k • lateral U k (leftMetric (C:=C)) (Σr k) + b k • lateral U k (rightMetric (C:=C)) (Σr k) + d k • (r • customDer (x₀ k) timeAxis (testScalar U.curve k) (Σr k)) :=by
    filter_upwards [Q.quotes,Q.fits] with k hk he r
    let v:Axis:=timeAxis
    let C₀ := U.curve.U k 4
    let w:=focus 4 (testScalar U.curve k)
    let y:=separated r
    let L'(i:Axis)(z:(E).Field 4):= customDer (S:=S) y i (C₀ z) w
    have hp : y∈conf _:= room_conf _ _ _ _ _ (room_separated _ (U.curve.positive k).le) (U.curve.positive k) one_pos
    choose L hL using fun i:Axis=>(customDer_linear (e:=4) y w i hp U.E U.diff)
    have hL' (i):L' i=fun z=>L i (C₀ z):= funext (fun z=>hL i (C₀ z))
    suffices ht : (∑ i:Axis,L' i (pullY U k i v))=(a k • (∑ i:Axis,L' i (leftMetric i v))+b k • (∑ i:Axis,L' i (rightMetric i v)))+d k • (L' v s₀) by
       convert congr_arg (r • ·) ht using 1
       · congr 1; apply Finset.sum_congr rfl; intro i _; exact congr_arg (customDer y i · w) (LinearEquiv.apply_symm_apply (U.curve.U k 4) _).symm
       unfold lateral; rw [smul_add,smul_add]; simp_rw [smul_comm r]; rfl
    conv_lhs => rw [Finset.sum_congr rfl (fun x _=>congr_arg (L' x) (hk x v)), Finset.sum_congr rfl (fun x _=>congr_fun (hL' _) _)]
    simp only [map_add, apply_ite C₀, map_zero, RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul]
    simp only [apply_ite (L _)]
    simp only [map_smul,map_zero]
    simp only [← hL]
    simp_rw [Finset.sum_add_distrib, ← Finset.smul_sum, show C₀ ((E).unit 4)=_ from he]
    rw [Finset.sum_congr rfl (fun i _=> congr_arg ((g k i v) • ·) (custom_derivative_unit U.F y w i hp)),Finset.sum_congr rfl (fun i _=> smul_zero (g k i v)),Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,L',add_zero]
lemma heat : ∀ᶠ k in atTop, (U.curve.r k)^4 • focus 4 (theta U.F 0)=(4*d k) • (Σr k):=by
   filter_upwards [Q.quotes,Q.fits] with k hk he
   rw [focus_eq,focus_eq]
   let Y:=U.curve.U k 4; let r:=U.curve.r k; let K:=centering S 4
   have hK :theta U.F 0=∑ i:Axis,U.F.sector.energy i i:=by unfold theta withoutMean; simp
   have hJ : ∑ i:Axis,leftMetric (C:=C) i i=0:=by
      simp only [leftMetric,if_true,metric0, Finset.sum_neg_distrib, show (∑ x, canonicalStress C.labels x x)=0 from by simpa [torch] using torch_traceless C.labels 1,neg_zero]
   rw [hK,map_sum,Finset.smul_sum]; simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ), ←map_smul]
   have hu i j:=congr_arg Y (hk i j)
   simp_rw [pullY, RCLike.real_smul_eq_coe_smul (K:=ℂ), show ∀ (v:S.Field 4), Y ((U.curve.U k 4).symm v)=v from Y.apply_symm_apply] at hu
   simp only [hu,if_true,map_add,map_smul,rightMetric,map_zero,smul_zero,add_zero, show Y ((E).unit 4)=_ from he, Next.UVStress.const_out U.F.room.kernel.laws, smul_zero,add_zero, Finset.sum_add_distrib,← Finset.smul_sum,← map_sum,hJ,map_zero,zero_add,smul_zero]
   rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, map_smul, map_smul]
   change (↑(↑(d k):ℝ) : ℂ) • (↑4 : ℂ) • _=  ((↑(4*d k):ℂ)) • _
   push_cast; unfold testScalar; dsimp only [Y]; module
def βProbe (k) := (U.curve.r k) • customDer (separated (U.curve.r k)) timeAxis (testScalar U.curve k) (focus 4 (testScalar U.curve k))
def leftProbe (c:ℕ→ℝ) (k:ℕ) := lateral U k (leftMetric (C:=C)) (focus 4 (testScalar U.curve k)) / (↑(c k):ℂ)^2
def totalProbe (c:ℕ→ℝ) (k:ℕ) := leftProbe (U:=U) c k + lateral U k (rightMetric (C:=C)) (focus 4 (testScalar U.curve k)) / (↑(c k) : ℂ)^2
local notation "μd" => theoryDensity G
local notation "b0" => anomalyCoefficient G
omit Q in
lemma requires : Tendsto (βProbe (U:=U)) atTop (𝓝 ↑(8*μd)) := convergence_rate U.curve U.F.room.kernel (fun R=>U.jets 2 4 1 R)
lemma combined (κ:ℕ→ℝ) : ∀ᶠ k in atTop, -(d k/((κ k)^2)) • βProbe (U:=U) k = b k • totalProbe (U:=U) κ k + (a k-b k) • leftProbe (U:=U) κ k:= by
   filter_upwards [Q.terms] with k hk
   let r:=U.curve.r k; let Am:=lateral U k (leftMetric (C:=C)) (Σr k); let B:=lateral U k (rightMetric (C:=C)) (Σr k)
   have he:= conservation_pairs U.F (Σr k) timeAxis (x₀ k) (room_conf _ _ _ _ _ (room_separated _ (U.curve.positive k).le) (U.curve.positive k) one_pos) r
   change _ = _ at hk; rw [he,smul_zero] at hk
   change 0 = a k • Am + b k • B + d k • (βProbe (C:=C) (U:=U) k) at hk
   have hh : (-d k) • (βProbe (U:=U) k)= b k • (Am+B) + (a k-b k) • Am:= by rw [neg_smul,neg_eq_iff_add_eq_zero]; rw [sub_smul,smul_add]; rw [hk]; abel
   change _ = _ • (Am/(↑(κ k):ℂ)^2 + B/(↑(κ k):ℂ)^2) + _ • (Am/_) -- denom type
   have h:= congr_arg (fun z=> ((κ k)^2)⁻¹ • z) hh
   simpa only [smul_smul,smul_add, smul_smul,Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_mul,div_eq_mul_inv,add_mul,neg_mul, mul_neg, mul_assoc,mul_comm,mul_left_comm] using! h

open Asymptotics
lemma determines (h:G.Simple)(κ:ℕ→ℝ)(hk : Tendsto (totalProbe (U:=U) κ) atTop (𝓝 (↑(4*b0*μd):ℂ))) (hB : leftProbe (U:=U) κ =O[atTop] (fun _=> (1:ℝ))) : Tendsto (fun k=>d k/(κ k)^2) atTop (𝓝 (-b0/2)):=by
   obtain ⟨C',hc⟩:= hB.bound
   have hr : Tendsto (fun k:ℕ=>(a k-b k) • (leftProbe (U:=U) κ k)) atTop (𝓝 (0:ℂ)):=
      squeeze_zero_norm' ((show ∀ᶠ k:ℕ in atTop, ‖leftProbe (U:=U) κ k‖ ≤ C' *‖(1:ℝ)‖ from hc).mono (fun k hk=> by rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (by simpa using! hk) (abs_nonneg _))) (a:=fun k=>|a k-b k| * C') (by
        simpa using! (Q.primaryA.sub Q.primaryB).abs.mul_const C')
   have hh := (Q.primaryB.smul hk).add hr
   have hρ:0<(μd) := theoryDensity_pos h
   have hv:(↑(8*μd):ℂ)≠0:= by exact_mod_cast (show (8:ℝ)*μd≠0 from (mul_pos (by norm_num) hρ).ne')
   let z:=βProbe (U:=U); have h₀ := (requires (U:=U)).eventually_ne hv
   have ht : Tendsto (fun k:ℕ=>Complex.re (-((b k • totalProbe (U:=U) κ k + (a k-b k) • leftProbe (U:=U) κ k) / z k))) atTop (𝓝 (-b0/2)):=by
      convert Complex.continuous_re.continuousAt.tendsto.comp ((hh.div (requires (U:=U)) hv).neg) using 1
      · rfl
      · rw [one_smul,add_zero,← ofReal_div, ← ofReal_neg,ofReal_re,show -(4*b0*μd / (8*μd))=-b0/2 by field_simp;ring]
   apply ht.congr'
   filter_upwards [Q.combined κ,h₀] with k hx he
   change z k≠0 at he; rw [← hx, Complex.real_smul,mul_div_cancel_right₀ _ he, Complex.ofReal_neg,neg_neg, Complex.ofReal_re]
end Quota
end YM.Trace
