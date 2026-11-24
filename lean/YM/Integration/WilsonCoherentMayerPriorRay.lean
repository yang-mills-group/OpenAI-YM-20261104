import YM.Integration.WilsonCoherentMayerPriorStratum

/-! The complete signed path token has bounded radial derivatives at every real field parameter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorRay
open Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped Classical BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

def curve {k:ℕ} (T:Token G n (fun v=>(D v).Mood) k) (x:TestSpace D)(a:Directions G n)(t:ℝ):ℂ:=
  T.read x (field a t)

omit [DecidableEq V] in
theorem roster {k:ℕ}(T:Token G n (fun v=>(D v).Mood) k)(x:TestSpace D)(a:Directions G n):
    curve T x a=fun t=>∑b:Fin k→G.ColorIndex,T.gem b x • read a T.root (letters (T.re x) b) t:=by
  funext t
  simp only [curve,Token.read,Token.touch,Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_eq_mul,mul_comm (T.gem b x)]
  apply congrArg (fun u:ℂ=>u*T.gem b x)
  change (∏i:Fin k,(((T.path i).atSite (field a t) T.root (b i):ℝ):ℂ))=
    ((List.ofFn fun i=>(T.path i,b i)).map (WilsonSlotContactTruncation.coord (field a t) T.root)).prod
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_apply,WilsonSlotContactTruncation.coord]

omit [DecidableEq V] in
theorem smooth {k:ℕ}(T:Token G n (fun v=>(D v).Mood) k)(x:TestSpace D)(a:Directions G n):
    ContDiff ℝ ω (curve T x a):=by
  rw [roster]
  exact ContDiff.sum fun b _=>(read_smooth a T.root (letters (T.re x) b)).const_smul _

def wage (width A:ℝ)(j:ℕ):ℝ:=(j.factorial:ℝ)*(2*A/width)^j

theorem length {length fall:ℕ}(le:length≤fall){width A:ℝ}(hw:0<width)(ha:0≤A)(j:ℕ):
    (2*(length:ℝ)*A)^j≤Real.exp (width*fall)*wage width A j:=by
  have hf:0<(j.factorial:ℝ):=Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h:=(div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (width*(length:ℝ)) (by positivity) j)
  have hle:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (length:ℝ)≤fall by exact_mod_cast le) hw.le)
  calc
    _ = (width*(length:ℝ))^j*(2*A/width)^j:=by rw [←mul_pow];congr 1;field_simp
    _ ≤ (Real.exp (width*fall)*(j.factorial:ℝ))*(2*A/width)^j:=
      mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_right hle hf.le)) (by positivity)
    _ = _:=by unfold wage;ring

include H in
theorem bounded {i:ℕ}{T:Token G n (fun v=>(D v).Mood) (P.rank i)}(ht:P.packet i=some T)
    (x:IndependentTests D)(a:Directions G n){A:ℝ}(ha:0≤A)(available:∀e,speed a e≤A)(j:ℕ)(t:ℝ):
    ‖iteratedDeriv j (curve T (testInclusion D x) a) t‖≤
      (T.coin*Real.exp (width*T.fall))*wage width A j:=by
  let z:=testInclusion D x
  let L:=T.re z
  have regular (b:Fin (P.rank i)→G.ColorIndex):=read_smooth a T.root (letters L b)
  have rows (b:Fin (P.rank i)→G.ColorIndex):
      ‖iteratedDeriv j (read a T.root (letters L b)) t‖≤ (2*(L.length:ℝ)*A)^j:=
    (product a T.root _ t j).trans (pow_le_pow_left₀
      (priced L T.root a ha (fun _ e _=>available e) b).1 (priced L T.root a ha (fun _ e _=>available e) b).2 j)
  have hi:=(H.paths i T ht z).1
  have htaylor:=length hi H.width_pos ha j
  change ‖iteratedDeriv j (curve T z a) t‖≤_
  rw [roster,iteratedDeriv_fun_sum (fun b _=>((regular b).const_smul (T.gem b z)).contDiffAt.of_le (by simp))]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑b,‖T.gem b z‖*(2*(L.length:ℝ)*A)^j:=by
      apply Finset.sum_le_sum
      intro b _
      change ‖iteratedDeriv j ((T.gem b z) • read a T.root (letters L b)) t‖≤_
      rw [iteratedDeriv_const_smul ((regular b).contDiffAt.of_le (by simp)) (T.gem b z),norm_smul]
      exact mul_le_mul_of_nonneg_left (rows b) (norm_nonneg _)
    _ ≤ T.coin*(Real.exp (width*T.fall)*wage width A j):=by
      rw [←Finset.sum_mul]
      exact mul_le_mul ((H.coefficient i T ht).2 x) htaylor (by positivity) (H.coefficient i T ht).1
    _ = _:=by ring

end YM.Integration.WilsonCoherentMayerPriorRay
