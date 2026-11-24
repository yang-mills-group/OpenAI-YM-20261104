import YM.OPE.Compatible.Nock.Brook
/-!
# hessian in forest coordinates
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B}{A:Alps B Q i l} (H: Even n.val) (T:Plot H)
local notation "TK" => Keys G (Limb H)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
abbrev BumpV (G:Gauge): Keys G T.Free→ₗ[ℝ] Keys G (Limb H):= T.rollX+ (T.palmL G).comp (landFuse H T G)
def compass (G:Gauge): (Keys G T.Free × Keys G T.Stable) ≃ₗ[ℝ] Keys G (Limb H) where
    toFun p:= BumpV H T G p.1+ T.palmL G p.2
    map_add' u v:=by simp only [Prod.fst_add,Prod.snd_add,map_add]; abel
    map_smul' c u:=by simp [smul_add]
    invFun x:= (T.slab G x, T.porch G x - landFuse H T G (T.slab G x))
    left_inv:= by rintro ⟨x,y⟩; simp [BumpV]
    right_inv x:=by simp only [BumpV,LinearMap.add_apply,LinearMap.comp_apply,map_sub]; rw [add_assoc, add_sub_cancel]; exact T.nestPoints x
@[simp] lemma firstC (x: FD)(y:DK): T.slab G (compass H T G (x,y))=x:=Prod.mk.inj (((compass H T G).symm_apply_apply (x,y))) |>.1 -- defeq?
lemma slopeJet {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](P:E→F)(hf:ContDiffAt ℝ ∞ P 0)(hp:P 0=0)(u:F→ℝ)(he:Radial.Stationary u): iteratedFDeriv ℝ 2 (u ∘ P) 0= (iteratedFDeriv ℝ 2 u 0).compContinuousLinearMap fun _=>(fderiv ℝ P 0):=by
      -- FaaD
      have hg:fderiv ℝ u 0=0:=by ext i; have ht:= he.base1 i; unfold jet at ht; simp only [iteratedFDeriv_one_apply,Nat.factorial_one,Nat.cast_one, inv_one,one_mul] at ht; exact ht
      have p:ContDiffAt ℝ ((2:ℕ):WithTop ℕ∞) _ _:=hf.of_le (WithTop.coe_le_coe.mpr le_top); have t:ContDiffAt ℝ ((2:ℕ):WithTop ℕ∞) u (P 0):=hp.symm ▸ he.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
      have hx:fderiv ℝ (u ∘ P) =ᶠ[𝓝 0] fun z=>(fderiv ℝ u (P z)).comp (fderiv ℝ P z):=by
          filter_upwards [p.eventually (by simp),p.continuousAt.eventually (t.eventually (by simp))] with i a b; exact fderiv_comp i (b.differentiableAt (by norm_num)) (a.differentiableAt (by norm_num))
      have hd := (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
      have hz:= (he.smooth.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp); have hv:DifferentiableAt ℝ (fderiv ℝ u) (P 0):= hp.symm ▸ hz
      have hf':= hf.differentiableAt (by simp); ext1 v; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply,hx.fderiv_eq, fderiv_clm_comp (show DifferentiableAt ℝ (fun z=> fderiv ℝ u (P z)) 0 from hv.comp 0 hf') hd,show fderiv ℝ (fun z=> fderiv ℝ u (P z)) 0=_ from fderiv_comp 0 hv hf',hp,hg]; simp
lemma compass_charge (x:FD)(y:DK): rinse H (T.dtex G (compass H T G (x,y)))= rinse H (T.palmFrame G y):=by
       unfold compass; change rinse H (T.dtex G ((T.rollX x +_)+_)) = _; simp only [map_add, T.keep_tex]; change rinse H _ + rinse H (T.palmFrame G _) + rinse H (T.dtex G (T.palmL G _)) = _ -- ensure type
       have he:= drains H T x; unfold certain at he;rw [map_add] at he; nth_rw 1 [add_comm (rinse H _),he, zero_add];rfl
lemma mast (X:Lit H A b)(_hx:4≤ i): Cel (X.s.f ∘ (T.skews G).gradient):=by
       let W:= T.skews G; apply Radial.quadratic_min; intro x hp; have hz:(T.dtex G x)≠0:=by intro h; exact hp (T.dtexInj (h.trans (by rw [map_zero])))
       have h0: jet (X.s.f ∘ W.gradient) 2 x=jet X.s.f 2 (T.dtex G x):=by unfold jet; rw [slopeJet W.gradient W.gradC W.grad0 X.s.f X.s.F]; rfl
       obtain ⟨c,hc,h⟩:=X.s.bright; exact h0.symm ▸ lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hz))) (h (T.dtex G x))
end YM.OPE.Cascade.Glass
