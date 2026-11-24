import YM.Integration.WilsonSeparatedOriginalSlabFourierSymbol
import Mathlib.Analysis.Calculus.SmoothSeries

/-! On the genuine compact chart the Fourier sum recovers each entire Fréchet derivative tensor after a real linear physical change of coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierJets
open Filter Set Function Metric UnitAddTorus WilsonSeparatedOriginalSlabFourierOrbit WilsonSeparatedOriginalSlabFourierLattice
open WilsonSeparatedOriginalSlabPeriodCells
open scoped Topology BigOperators Classical ContDiff
variable {J E:Type*}[Fintype J][NormedAddCommGroup E][NormedSpace ℝ E]

def wave (P:E→L[ℝ]Room J)(k:J→ℤ)(x:E):ℂ:=mFourier k (wrap (P x))

private theorem base (k:J→ℤ):ContDiff ℝ ∞ (fun x:Room J=>mFourier k (wrap x)):=by
  simp_rw [WilsonSeparatedOriginalSlabFourierSymbol.source]
  exact ((Complex.ofRealCLM.contDiff.mul contDiff_const).cexp).comp (WilsonSeparatedOriginalSlabFourierSymbol.arm k).contDiff

private theorem drawn (P:E→L[ℝ]Room J)(k:J→ℤ)(c:ℂ):ContDiff ℝ ∞ (c • wave P k):=
  ((base k).comp P.contDiff).const_smul c

private theorem entry (P:E→L[ℝ]Room J)(k:J→ℤ)(m:ℕ)(c:ℂ)(x:E):
    ‖iteratedFDeriv ℝ m (c • wave P k) x‖≤((2*Real.pi)^m*‖P‖^m)*(‖c‖*height k^m):=by
  have hw:ContDiff ℝ ∞ (wave P k):=(base k).comp P.contDiff
  rw [iteratedFDeriv_const_smul_apply (a:=c) (f:=wave P k) (x:=x) (contDiff_infty.mp hw m).contDiffAt,norm_smul]
  change ‖c‖*‖iteratedFDeriv ℝ m ((fun y:Room J=>mFourier k (wrap y)) ∘ P) x‖≤_
  rw [P.iteratedFDeriv_comp_right (contDiff_infty.mp (base k) m) x (i:=m) le_rfl]
  have core:= (ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ m (fun y:Room J=>mFourier k (wrap y)) (P x)) (fun _=>P)).trans
    (mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalSlabFourierSymbol.original k m (P x)) (Finset.prod_nonneg (fun _ _=>norm_nonneg P)))
  refine (mul_le_mul_of_nonneg_left core (norm_nonneg c)).trans_eq ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring

theorem original (P:E→L[ℝ]Room J){a:Room J}{ρ:ℝ}{f:Room J→ℂ}(smooth:ContDiff ℝ ∞ f)
    (small:ρ+ρ<1)(live:support f⊆closedBall a ρ)(e:ℕ){B:ℝ}(hB:0≤B)(lo:∀x,‖f x‖≤B)
    (hi:∀x,‖iteratedFDeriv ℝ (WilsonSeparatedOriginalSlabFourierBudget.order J e) f x‖≤B)
    (m:ℕ)(he:m≤e)(x:E)(central:ρ+dist (P x) a<1):
    let F:=WilsonSeparatedOriginalSlabCompactFourier.profile smooth small live
    HasSum (fun k:J→ℤ=>iteratedFDeriv ℝ m (mFourierCoeff F k • wave P k) x) (iteratedFDeriv ℝ m (f ∘ P) x):=by
  let F:=WilsonSeparatedOriginalSlabCompactFourier.profile smooth small live
  let program (k:J→ℤ):E→ℂ:=mFourierCoeff F k • wave P k
  let costs (h:ℕ)(k:J→ℤ):ℝ:=((2*Real.pi)^h*‖P‖^h)*(‖mFourierCoeff F k‖*height k^e)
  obtain ⟨income,_,values⟩:=WilsonSeparatedOriginalSlabCompactFourier.original smooth small live e hB lo hi
  have purchased (h:ℕ):Summable (costs h):=income.mul_left _
  have bound (h:ℕ)(k:J→ℤ)(y:E)(hk:(h:ℕ∞)≤(e:ℕ∞)):‖iteratedFDeriv ℝ h (program k) y‖≤costs h k:=by
    refine (entry P k h _ y).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (by positivity))
    exact pow_le_pow_right₀ (active k) (by exact_mod_cast hk)
  have hx:(fun y:E=>∑'k:J→ℤ,program k y)=ᶠ[𝓝 x] (f ∘ P):=by
    have nearby:∀ᶠy in 𝓝 x,ρ+dist (P y) a<1:= (isOpen_lt (continuous_const.add (P.continuous.dist continuous_const)) continuous_const).mem_nhds central
    filter_upwards [nearby] with y hy using (values (P y) hy).tsum_eq
  have same:iteratedFDeriv ℝ m (fun y=>∑'k:J→ℤ,program k y) x=iteratedFDeriv ℝ m (f ∘ P) x:= (hx.iteratedFDeriv ℝ m).self_of_nhds
  have hm:(m:ℕ∞)≤(e:ℕ∞):=by exact_mod_cast he
  have eq:=iteratedFDeriv_tsum_apply (f:=program) (v:=costs) (N:=(e:ℕ∞)) (fun k=>contDiff_infty.mp (drawn P k _) e)
    (fun h _=>purchased h) bound hm x
  rw [←same,eq];exact ((purchased m).of_norm_bounded (fun k=>bound m k x hm)).hasSum

end YM.Integration.WilsonSeparatedOriginalSlabFourierJets
