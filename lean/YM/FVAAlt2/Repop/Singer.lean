import YM.FVAAlt2.Repop.Charts
/-!
# Rendered vacuum carrying full bank backwards to native coupling, fixed-measure stepwise

GradeAt3 of W here (extra interaction of fluctuation order at least one). No flag,
 no seal assertion of Standard. `qlocal` will need actual analytic/momentum-of-loop
 reconciliation (including checking size of relevant curvature e=2 proceeds to allow Standard *with* winding residual; GradeAt3 at fixed period does **not** assume it), even apart from locality of rendering. Also Regional.bright etc only formal orientation.Here work purely with formal body incl paths, low-only aperture real.K.Probe. Use nonordinary prefactor via $Shadow$. Sign proof and no imaginary vacuum representation.Makes.Size.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Repop
open RG Wilson Tree Exterior Lattice Precision MeasureTheory
open Comparison.RG02 Symmetry Symmetry.Orbit Comparison.RG02.Moving Moving.Path Moving.Shift Valence Assembly Adjacent Bulk
open Filter Function Set Finset Push.SectorMeasure Gauge Integral ConnectedActivityE6 Matrix
open PertExtension.Series PertExtension.Series.Tested
open Diagram Diagram.Formal Binding Booth Booth.Uniforms Prim PowerSeries
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G : Gauge} {n:Side} {V:Type}
variable {δ γ:ℝ}
-- trick to track VALUE(1,x). works any field & kth order through curvature.
lemma diagonal {E L:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup L][NormedSpace ℝ L] [FiniteDimensional ℝ E]
    (k:ℕ) (F:ℝ×E→ L)(h: ∀ x:E, Assembly.jet F k (1,x)=0): ∀ x, Assembly.jet F k x=0:= by
   have hv : Continuous (jet F k) := (Tensor.diag_smooth (Tensor.coeff F k 0) ω).continuous
   let a (y:ℝ×E):=jet F k y
   have he (x:ℝ)(y:E)(hh:x≠0) : a (x,y)=0:=by
      unfold a; rw [show (x,y)= x • ((1:ℝ),x⁻¹ • y) from (by apply Prod.ext (show x=x*1 from by simp); change y= x • x⁻¹ • y; rw [smul_smul,mul_inv_cancel₀ hh,one_smul]), Assembly.Clipper.weight,h,smul_zero]
   rintro ⟨x,y⟩; by_cases hx:x=0; swap; · exact he x y hx
   subst x; have hc: Tendsto (fun t:ℝ=> a (t,y)) Laplace.along (𝓝 (a (0,y))) := (hv.continuousAt.comp (f:=fun t:ℝ=>(t,y)) (continuousAt_id.prodMk continuousAt_const)).mono_left nhdsWithin_le_nhds
   exact tendsto_nhds_unique hc ( tendsto_const_nhds.congr' (Tested.eventually_pos.mono (fun t ht=> (he t y ht.ne').symm)) )

local notation "X"=> fieldDir G n 1
local notation "A"=> Config G n
local notation "E"=> (ℝ × fieldDir G n 1)
variable (C: UnitCost)(p:RG.Clip)(T:PathData G)(P:Diagram.Orders (Pin n G))(r:ℕ) (H : Bright P T p r)
variable (χ:Chi) {b α Ω:ℝ} (hc:Reliable G δ γ) (hT: T.Bounds p b α Ω)
local notation "T'" => cloth p T P
local notation "F"=> garment C (T') r 2 χ δ
-- output W.vac(t,U)
def singer (δ:ℝ)(t:ℝ)(U:A):ℝ:= -(garment C (Uniforms.cloth p T P) r 2 χ δ t U).re- mainTerm p T U -t^2*Precision.loop T U
local notation "M"=> singer C p T P r χ δ
include H
lemma oriented_zero (x:X): T' 0 x = - Complex.ofReal (Assembly.jet (mainTerm p T ∘ represent) 2 x):=by unfold cloth; rw [Binding.flavor_dark _ (Binding.vacuum_lo _ H.paid) _,if_pos rfl,Complex.ofReal_zero, add_zero]
lemma till (x:X) : Adjacent.born T' C.inverseCurve 0 r 0 x=T' 0 x:= by
    have hp:= Adjacent.ledger (U:=(Uniforms.cloth p T P)) C.inverseCurve 0 r H.valid.heft 0 (Nat.zero_le _) x; rw [range_zero,sum_empty,add_zero] at hp; exact hp
include hc
lemma porthole (x:X) : Assembly.jet (Bulk.projected (garment C (T') r 2 χ δ)) 2 (1,x)= - Complex.ofReal (Assembly.jet (mainTerm p T ∘represent) 2 x):=by
    rw [show Assembly.jet (Bulk.projected F) 2 (1,x)=_ from invoice C T' r 2 H.sheet H.valid hc χ x 0 (Nat.zero_le _), till C p T P r H,oriented_zero p T P r H x]
-- shifted π map for all orders; no issue clipping
local notation "τ"=> C.rating
local notation "υ"=> (mainTerm p T ∘ (represent (G:=G) (n:=n)))
local notation "Y"=> Bulk.projected M
include hT
lemma readyChart : GradeAt 3 Y := by
   let L:= Bulk.projected (F); have hp:GradeAt 2 L:= warm C (T') r 2 H.sheet H.valid hc χ
   have hF:= GradeAt.linear_contact (-Complex.reCLM) hp
   let P':= (-Complex.reCLM) ∘ L; let q:E→L[ℝ] X:= ContinuousLinearMap.snd ..; let k:= υ ∘ q
   let J:E→ℝ:= fun x=> x.1^2*Precision.loop T (represent x.2)
   have hh:GradeAt 2 (υ):=by
      have ht':ContDiffAt ℝ ω υ 0:= Extra.Iteration.Calibration.main_jet hT
      constructor
      · exact ht'
      intro i hi; ext1 y; interval_cases i
      · rw [iteratedFDeriv_zero_apply]; exact Bulk.main_origin p T hT
      rw [iteratedFDeriv_one_apply]; rw [show fderiv ℝ υ 0=0 from Bulk.main_first p T hT]; rfl
   have hk: GradeAt 3 J:= by
      have hs : GradeAt 1 ( loop T ∘ (represent (G:=G) (n:=n)) ):= (GradeAt.anchored (Bulk.loop_smooth (m:=n) p T hT) (show loop T (represent (0:X))=0 by rw [link_one]; exact Bulk.loop_origin p T hT))
      exact (GradeAt.shifts (Prod.fst : E→ℝ) contDiffAt_fst rfl 2).mul (hs.coarse (g:=q) q.contDiff.contDiffAt q.map_zero)
   have hv:Y = P'-k-J:=rfl
   have hU: GradeAt 2 Y:= hv ▸ ((hF.sub (hh.coarse (g:=q) q.contDiff.contDiffAt q.map_zero)).sub (hk.lower (by omega))) -- hx elaboration
   have hu' : GradeAt 2 k:= hh.coarse (g:=q) q.contDiff.contDiffAt q.map_zero
   refine ⟨hU.smooth,fun i hi=>?_⟩; by_cases he:i<2; · exact hU.vanish i he
   have hm:i=2:=by omega
   subst i
   have hz(x:X): Assembly.jet Y 2 (1,x)=0:=by
      unfold Assembly.jet;rw [hv, iteratedFDeriv_sub_apply  (f:=P'-k) ( (hF.smooth.sub hu'.smooth).of_le le_top ) (hk.smooth.of_le le_top),hk.vanish 2 (by omega),sub_zero, iteratedFDeriv_sub_apply (f:=P') (hF.smooth.of_le le_top) (hu'.smooth.of_le le_top) ]; simp_rw [ _root_.sub_apply,smul_sub]; change Assembly.jet P' 2 (1,x)-Assembly.jet k 2 (1,x)=_
      rw [show jet P' 2 (1,x)=_ from (Assembly.jet_apply_left (-Complex.reCLM) L 2 (hp.smooth.of_le le_top) (1,x)).symm,show Assembly.jet k 2 (1,x)=_ from Assembly.jet_continuous_right q (hh.smooth.of_le le_top) (1,x), show jet L 2 (1,x)=_ from porthole C p T P r H χ hc x]; rw [show q (1,x)=x from rfl]; simp
   apply Tensor.ext_diag _ _ (YM.Analysis.sym_Jet (hU.smooth.of_le le_top)) (fun _ _=>rfl)
   funext x; change _= (0:ℝ); exact mul_left_cancel₀ (a:= (↑(Nat.factorial 2):ℝ)⁻¹) (by positivity) (( diagonal 2 (Y) hz x ).trans (mul_zero _).symm)
lemma wearing (t:ℝ): GaugeInvariant (M t):= by
    intro f U; unfold singer; rw [Work.F05.mainTerm_gauge hT,Work.F05.loop_gauge hT, gauged C T' r 2 H.sheet H.valid hc χ t f U]; -- T' parse
lemma pose (t:ℝ) : Envelope (M t):= by
    apply Push.SectorMeasure.Env.compact -- inspect
    have ht : Continuous (F t):= earned_c C T' r 2 H.sheet H.valid hc χ t
    obtain ⟨hp,hq⟩:=Integral.main_continuous_π (f:=n) hT
    exact ((Complex.continuous_re.comp ht).neg.sub hp).sub ( hq.const_mul _ )

variable [DecidableEq V]{R: Marker.Census V}(W:Colors R G n)
-- $S.W` total cancellation with symbol.M.
omit hT in
lemma shine (hh : W.vac=M) (x:X): (Gala.feeAct p T C W x) =ᶠ[𝓝 0] - (Complex.reCLM ∘ supplies C 2 F (fun _=>x)) :=by
    filter_upwards [C.bright] with t ht
    unfold Gala.feeAct supplies Ribbon.fees; rw [hh]; unfold singer UnitCost.enter; simp only [Pi.neg_apply,Function.comp_apply,Complex.reCLM_apply, Complex.smul_re,smul_eq_mul]; field_simp; ring
-- Period prefix cost proof. $
lemma bearing (hh:W.vac=M)(e:ℕ)(he:0<e)(hp:e≤r) (x:X): - coeff (e+2) (Prim.tale (Gala.feeAct p T C W x))= coeff e ( Binding.flavor 2 (FreeResolvent.flatten x) P ):=by
    let k := supplies C 2 (F) (fun _=>x); have hx := (scopedAt C (T') r 2 H.sheet H.valid hc χ (fun _=>x) contDiffAt_const).left; have hv: ContDiffAt ℝ ω k 0:=hx; have hp' := entered C (T') r 2 H.sheet H.valid hc χ x e hp
    have ht: ContDiffAt ℝ ∞ (- (Complex.reCLM ∘ k) ) 0:= (( Complex.reCLM.contDiff.contDiffAt.comp _ hv ).neg).of_le le_top
    rw [tale_eq ht (shine C p T P r H χ hc W hh x),tale_jet, show -⇑Complex.reCLM ∘ k= (-Complex.reCLM) ∘ k from rfl ] -- precedence
    rw [ ← Assembly.jet_eq,← Assembly.jet_apply_left (-Complex.reCLM) k (e+2) (hv.of_le le_top)]
    unfold motion at hp';rw [show jet k (e+2) 1= T' e x from Nat.add_comm e 2 ▸ hp']; unfold Uniforms.cloth; simp [he.ne']

end YM.RegulatorIR.FVAAlt2.Repop
