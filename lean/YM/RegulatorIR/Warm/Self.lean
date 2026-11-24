import YM.RegulatorIR.Skein.Strikes
import YM.RegulatorIR.Oracle.Hamlet
import YM.RegulatorIR.Momentum.Crucible

/-!
# Unrepriced relative Hessian **on the cover**
Compute using chart W1 at large periodic copy. Pose joints here include
all fine links (not set on tree) individually; later support property of
propagation in walk is separate. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior FreeResolvent
open Push
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {P:Patch}{K:KernelChoices}{n c f:Side}
section Paths
variable (S:StepData c f)(z:Edge Cover)(x: Foot G→ℝ)(M:S.patch.Branches S.kernel G)
-- Probe pay on larger horizon, use cargo-of-reflag Row.S.H. matrix identity.
lemma pollen (d:Side)(H:Foot G→ℝ)(Y: In G (d*S.patch.L))(b:G.ColorIndex)(h:∀ i∈ (fringe S (z,b)).support, (collect G Y (around _ i.1)) i.2=H i):
    let T:=Prim.canopy S d; (probe T*ᵥ parts G 1 Y b) (wrap d z.1,coord z.2)= combo H (fringe S (z,b)):=by
 intro T; let R:=S.patch; let y: FreeResolvent.Vec G (d*S.patch.L) 1:= fun t=> Y (t.1,t.2.1) t.2.2
 let i:Long G.ColorIndex:=(z,b); let F:=fringe S i
 let G0:= linksQ G;let x:= blockQ G S.patch.L
 have h₁: (FreeResolvent.tensor G (probe T)*ᵥ y) (G0.swrap d i)=(probe T*ᵥ parts G 1 Y b) (wrap d z.1,coord z.2):=congr_fun (FreeResolvent.component_mul (probe T) y b) (wrap d z.1,coord z.2) -- order
 rw [← h₁,show probe T= probe (avenue S.patch S.kernel d) from rfl,← credited]
 rw [Oracle.Rubric S.patch S.kernel G d]; -- cargo notation
 let Q:= avenue S.patch S.kernel d
 change (ledgerRow G0 x (finer (fringe Q)) d*ᵥ y) (G0.swrap d i)=_
 have ht:= cargo_of (Long G.ColorIndex) G0 x i d (fringe Q) (fringe_inv Q G) y
 rw [ht]; change combo _ F= _
 rw [combo,Finsupp.linearCombination_apply, combo,Finsupp.linearCombination_apply]; refine Finset.sum_congr rfl (fun v hv=>congr_arg ((fringe S i) v • ·) ?_)
 change y (x.swrap d v)=H v;rw [show x.swrap d v= _ from v_same v S.patch.L d]; exact h v hv
-- Gard scale.Harm local. stencil fixed θ.
def rebus : G.Color:= WithLp.toLp 2 (fun j:G.ColorIndex=> combo x (fringe S (z,j)))
include M
lemma pesto : HasDerivAt (fun t:ℝ=> G.mat (pond S.patch S.kernel (win G (t • x)) z)) (G.colorMat (rebus S z x)) 0:=by
 let Q:= lantern S.patch z; let R(j:G.ColorIndex):= fringe S (z,j)
 let A:= Q∪ Finset.univ.biUnion fun i:G.ColorIndex=> (R i).support.image Prod.fst
 obtain ⟨n,h⟩:= ampleS S.patch A
 let f:= n*S.patch.L; let L:= ascend A f h; let g:= fun a:↥A=> timber G x a.val; let v:= Function.extend L g (fun _=>0)
 let Y: In G f:= fun y=> v (y.1,Exterior.axisEquiv.symm y.2); let W:=Prim.canopy S n
 have hp(e:Edge Cover)(h:e∈ A):collect G Y (around f e)=timber G x e:=by
    change v (_,axisEquiv.symm (coord _))= _; rw [show ∀ i:Axis, axisEquiv.symm (coord i)=i from fun i=> axisEquiv.symm_apply_apply i]; exact L.injective.extend_apply g (fun _=>0) ⟨e,h⟩
 have hj: rebus S z x=WithLp.toLp 2 (fun j:G.ColorIndex=> (probe W*ᵥ parts G 1 Y j) ((around n z).1,coord z.2)):=by
    unfold rebus; apply congr_arg;ext1 j
    symm; apply pollen S z n x Y j _; intro i hi
    exact congr_arg (fun b:G.Color=>b i.2) (hp i.1 (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,mem_univ _, Finset.mem_image_of_mem _ hi⟩)))
 rw [hj]; refine (Push.prices W M (around n z) (directive W) Y).congr_of_eventuallyEq (Eventually.of_forall fun t=>?_)
 dsimp only;rw [← show pond S.patch S.kernel (represent (t • Y) ∘ around f) z=W.prediction _ _ (around n z) from Prim.sunset S n _ _]; apply congr_arg; apply Prim.pond_low S.patch S.kernel M z
 intro i hi; rw [Function.comp_apply,Work.F03.represent_link]; unfold win; apply congr_arg G.lieExp; rw [timbers]; exact congr_arg (t • ·) (hp i (Finset.mem_union_left _ hi)).symm
-- path with both boards
def riddle (r:KFoot G→ℝ) : G.Color:= timber G (r ∘ Sum.inr) z - rebus S z (r∘Sum.inl)
def gear (a:KFoot G→ℝ) (t:ℝ):G.El:= win G (t • (a ∘ Sum.inr)) z * (pond S.patch S.kernel (win G (t • (a ∘ Sum.inl))) z)⁻¹
lemma gears_0 (a:KFoot G→ℝ) : gear S z a 0=1:=by
 have h:win G 0=1:=funext (fun i=> by unfold win; rw [timber_0];exact G.mat_lieExp_zero)
 unfold gear;rw [zero_smul,zero_smul,h,Prim.settledLow S M]; simp
lemma gears_s (a:KFoot G→ℝ): HasDerivAt (fun t:ℝ=> G.mat (gear S z a t)) (G.colorMat (riddle S z a)) 0:=by
 let W:= timber G (a ∘ Sum.inr) z;let v:= (a ∘ Sum.inl); let Y:= rebus S z v;let p(t:ℝ):= win G (t • (a ∘ Sum.inr)) z
 let q(t:ℝ):= pond S.patch S.kernel (win G (t • v)) z
 have he(t:ℝ): p t=G.lieExp (t • W):=by unfold p win; rw [timbers]; rfl
 have hf : HasDerivAt (fun t=>G.mat (p t)) (G.colorMat W) 0:=by simp_rw [he]; exact Binding.vertical_deriv _
 have hz:p 0=1:=by rw [he,zero_smul,G.mat_lieExp_zero]
 have hq:q 0=1:=by have hc:= gears_0 S z M a; change p 0*(q 0)⁻¹=_ at hc;rw [hz,one_mul] at hc;exact inv_eq_one.mp hc
 simp_rw [gear,G.mat_mul,G.mat_inv]
 apply (hf.mul (pesto S z v M).star).congr_deriv
 change G.colorMat W*star (G.mat (q 0))+ G.mat (p 0)*star (G.colorMat Y)=G.colorMat (W-Y)
 rw [hz,hq,G.mat_one,star_one,mul_one,one_mul, G.colorMat_skew,map_sub,sub_eq_add_neg]
lemma burnM (a:KFoot G→ℝ): coeff 2 (tale (flank (opi S Clocks.flat z) a))= S.kernel.penalty*(‖riddle S z a‖^2/2):=by
 let g:=flank (opi S Clocks.flat z) a
 have hp(t:ℝ) : g t/t^2=S.kernel.penalty*(G.price (gear S z a t)/t^2):=by unfold g flank opi; change 1*S.kernel.penalty * (G.price (gear S z a t))/t^2= _;ring
 have ht : Tendsto (fun t:ℝ=>g t / t^2) (𝓝[≠] 0) (𝓝 (S.kernel.penalty*(‖riddle S z a‖^2/2))) := by simp_rw [hp]; exact Tendsto.const_mul _ (Work.F03.price_limit (gears_0 S z M a) (gears_s S z M a))
 have hh:ContDiffAt ℝ 2 g 0 := ((Prim.locally S M Clocks.flat z).some.smooth_v a).of_le (WithTop.coe_le_coe.mpr le_top)
 obtain ⟨hr,hv⟩:= Work.F03.value_slope_of_sq_limit hh.continuousAt ht
 have hV:= tendsto_nhds_unique (Work.F03.taylor_limit_two hh hr hv.deriv) ht
 rw [← hV, tale_jet, jets_cap]; -- calc
 · unfold g; norm_num [Nat.factorial];ring
 exact (Prim.locally S M Clocks.flat z).some.smooth_v a
end Paths
end YM.RegulatorIR.Warm
