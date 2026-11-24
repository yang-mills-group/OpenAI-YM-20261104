import YM.FVAAlt2.Periodic.Rent
import YM.Comparison.RG02.Adjacent.Caliber
/-!
# Full-torus conditional translated only in LOG coordinates, with scaled common frame.Exact input

This is NOT identical to the native parser's `release V bi` chart. Uses
 `exp[g ⋅ (w + K.b' x + linearCopy(V))]` (at each bond), needed for identifying with Reel. In particular higher order terms change from BCH. Derive native prescription equivalence by real analytic saddle calculation later. Retains ONE tag throughout all uses.Then apply `Order.ratio` etc with fields, notation vacuum price t-expressed. Need multiply by chartCost and Haar. Positive integer powers.W
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Aperture
open Set Filter Finset MeasureTheory Function Lattice RG Precision Wilson Exterior Tree Bid
open PertExtension.Series Bulk Adjacent Order Assembly Marker Multi YM.Next.SectorChange Integral Gaussian
open Work.F03
open scoped Topology ContDiff Classical Matrix BigOperators ENNReal NNReal Matrix.Norms.Frobenius
variable {c f: Side}{G:Gauge}{P: PathData G}{p:Clip}{O:ChartRatio G}{S:StepData c f}
variable (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(w:S.Choices)(C:UnitCost)
variable {V:Type} [DecidableEq V]{R:Census V}(W:Bulk.Colors R G f)
-- coords share second jet with Θ
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=>Bulk.Joint S F (G:=G)
local notation "L"=>Precision.Key F G→ℝ
local notation "ρ"=> C.enter
local notation "τ"=> C.rating

def alpha : Bulk.SliceDir S F G →L[ℝ] Logs G c f := fderiv ℝ (inclusion F) 0
def uniting : Bulk.Joint S F (G:=G) →L[ℝ] Logs G c f := (alpha F) ∘L (ContinuousLinearMap.snd ..)
lemma uniting_eq (z : T) : uniting F z=(z.2.1,stretch F z.2) := inclusion_deriv F z.2
def opens (z: T):= represent (uniting F z).2
-- from the absolute port.Person
@[simp] lemma unitOpen : opens F (0:T)=1:=by unfold opens;rw [map_zero];exact link_one
-- bond angle leg (NOT absolute site part only where free)
def freedom : Y→L[ℝ] AxisChart G F:= LinearMap.toContinuousLinearMap { toFun:=fun y i=> y (i.val.1,coord i.val.2), map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
def starship : T→L[ℝ] AxisChart G F:= freedom (S:=S) F ∘L ContinuousLinearMap.snd ℝ X Y ∘L uniting F
lemma free_at (z:T)(i:F.Free): starship F z i= linearCopy S.ratio (collect G z.2.1) i + z.2.2 i:=by
    change freedom F (uniting F z).2 i=_; rw [uniting_eq]; unfold freedom LinearMap.toContinuousLinearMap stretch; dsimp; rw [show axisEquiv.symm (coord i.val.2)=i.val.2 from axisEquiv.symm_apply_apply _, dif_neg i.property]
lemma clamped (z:T): F.drape (release (1:F.Slice G) (starship F z))= opens F z:=by
    funext i; unfold opens; rw [represent_link, uniting_eq] -- fix
    by_cases he:i∈F.trunks
    · rw [show F.drape (release (1:F.Slice G) (starship F z)) i = 1 from F.on_tree _ ⟨i,he⟩]; simp only [stretch]; rw [show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _,dif_pos he, add_zero, linearCopy, if_pos (F.trunk_internal he),G.mat_lieExp_zero]
    rw [show F.drape (release (1:F.Slice G) (starship F z)) i = release (1:F.Slice G) (starship F z) (⟨i,he⟩:F.Free) from F.off_tree _ ⟨i,he⟩]; unfold release;rw [Pi.one_apply,mul_one]; apply congr_arg; change freedom F (uniting F z).2 _=_; rw [uniting_eq];rfl

def fineScore (_ :Bulk.Kernel S p P O)(z:T):ℝ:= Work.F03.flat S w p P (uniting F z)
def baseRatio(z:T) :ℝ:= ((τ z.1)^2)⁻¹
-- always charge actual path loop, and every color

def freshvac (z:T):ℝ:= W.vac (ρ z.1) (opens F z)
def reprc (_ :Bulk.Kernel S p P O) (z:T):ℝ:= loop P (opens F z)- Real.log (∏ i,O.J (starship F z i))
def adorn(z:T):ℝ:= (baseRatio F C z-1)*fineScore F w K z+ pillar (F:=F) z*reprc F K z +baseRatio F C z*freshvac F C W z
-- annotate argument order above

def core (_z:T):= fineScore F w K _z + adorn K F w C W _z
def scoreMark (j:Hot R)(z:T):ℂ := ((τ z.1)^ W.power j)⁻¹ • W.mark j (ρ z.1) (opens F z)

-- jets ≤2.Surprisingly exact match Surface not price.Smooth.
lemma fineHome : ContDiffAt ℝ ω (fineScore F w K) 0:=by
    obtain ⟨e,u,l,H⟩:=K.bounds; let H':=flat_smooth K.branches w (Work.F02.answer _ _ _ _ _ _ H); exact (show ContDiffAt ℝ ω (Work.F03.flat S w p P) (uniting F 0) from ((uniting F|>.map_zero).symm ▸ H')).comp _ (uniting F).contDiff.contDiffAt
-- may assume D.Fiscal then easy
variable (B : Bed)(h : YM.FVAAlt2.Period.Rent.Right p P f B)
include h
lemma no_shift : GradeAt 2 (fineScore F w K):=by
    obtain ⟨d,a,t,hB⟩:=K.bounds
    have hm:= YM.FVAAlt2.Period.Rent.moving_line K B h
    have hv := flat_smooth K.branches w (Work.F02.answer _ _ _ _ _ _ hB)
    -- through radial limit. no linear term Hess.Cov
    constructor
    · exact fineHome K F w
    have hh:= fineHome K F w
    have hx (x:T) : Tendsto (fun t:ℝ=> fineScore F w K (t • x)/t^2) (𝓝[≠] 0) (𝓝 (flatHess S B (uniting F x) (uniting F x)/2)):=by
       unfold fineScore Work.F03.flat flatHess; simp_rw [map_smul, add_div]; exact (hm _).add (noise_limit K.branches w (uniting F x))
    have ht (x:T):= value_slope_of_sq_limit (f:=fun t:ℝ=> fineScore F w K (t • x)) ( ContinuousAt.comp (g:=fineScore F w K) (f:=fun t:ℝ=> t • x) (x:=0) (by rw [zero_smul];exact hh.continuousAt) (continuousAt_id.smul continuousAt_const)) (hx x)
    intro i hi; ext1 x; interval_cases i
    · rw [iteratedFDeriv_zero_apply]; change fineScore F w K 0=0; simpa only [zero_smul] using (ht 0).1
    rw [iteratedFDeriv_one_apply]; exact (Push.side _ ((fineHome K F w).differentiableAt (by simp)) (x 0)).unique (ht (x 0)).2
lemma binding (x:T) : Assembly.jet (fineScore F w K) 2 x=Assembly.jet (Surface S p P F w) 2 x.2 :=by
    have hf:= no_shift K F w B h
    have hh (x:T): Tendsto (fun t:ℝ=> fineScore F w K (t • x)/t^2) (𝓝[≠] 0) (𝓝 (flatHess S B (uniting F x) (uniting F x)/2)):=by
       unfold fineScore Work.F03.flat flatHess; simp_rw [map_smul,add_div]; exact (YM.FVAAlt2.Period.Rent.moving_line K B h _).add (noise_limit K.branches w _)
    let W:=fineScore F w K; have hu: ContDiffAt ℝ 2 (W) 0:= (fineHome K F w).of_le le_top
    have he := (value_slope_of_sq_limit (f:=fun t:ℝ=> W (t • x)) (ContDiffAt.continuousAt (n:=2) (ContDiffAt.comp (g:=W) (f:=fun t:ℝ=> t • x) 0 (by rw [zero_smul];exact hu) (contDiffAt_id.smul contDiffAt_const))) (hh x)); have hv : fderiv ℝ W 0=0:= by
       apply ContinuousLinearMap.ext; intro y; have H:=(hf.vanish 1 one_lt_two); exact ((iteratedFDeriv_one_apply (f:=W) (x:=0) (fun _:Fin 1=>y)).symm).trans (congr_arg (fun (w': (T [×1]→L[ℝ] ℝ))=> w' (fun _=> y)) H) -- adjust
    have H:= tendsto_nhds_unique (taylor_limit_two (f:=fun t:ℝ=> W (t • x)) (ContDiffAt.comp (g:=W) (f:=fun t:ℝ=> t • x) 0 (by rw [zero_smul];exact hu) (contDiffAt_id.smul contDiffAt_const)) he.1 he.2.deriv) (hh x); rw [line_second hu hv] at H
    unfold Assembly.jet; rw [show (fun _:Fin 2=>x)=![x,x] from funext fun i=>by fin_cases i <;>rfl,show (fun _:Fin 2=>x.2)=![x.2,x.2] from funext fun i=>by fin_cases i <;>rfl]; apply congr_arg; have h0 := (YM.FVAAlt2.Period.Rent.controller K B h F w).2.2 x.2 x.2; replace H := div_left_inj' (by norm_num : (2:ℝ) ≠0) |>.mp H; rw [uniting_eq] at H; exact H.trans (h0.symm)
lemma home_adorn (hW : Well W) : GradeAt 3 (adorn K F w C W):= by
    obtain ⟨e,u,l,H⟩:=K.bounds; have hp : GradeAt 3 (freshvac (G:=G) F C W):= (hW.suppose_vac.coarse (g:=fun z:T=> (ρ z.1,(uniting F z).2)) ((C.here.comp (f:=Prod.fst) (0:T) contDiffAt_fst).prodMk (uniting F|>.contDiff.contDiffAt.snd)) (by rw [map_zero,Prod.fst_zero,C.borne]; rfl))
    let J (z : T) := ∏ i, O.J (starship F z i)
    have h0 : J 0=1 := by simp only [J,map_zero,Pi.zero_apply,K.ratio.anchored,prod_const_one]
    have hc : ContDiffAt ℝ ω J 0 := by
       unfold J; apply contDiffAt_prod; intro i _; have ho := K.ratio.germ 0 (Metric.mem_ball_self K.ratio.patch); exact (show ContDiffAt ℝ ω O.J (starship F 0 i) from by rwa [map_zero]).comp (f:=fun z:T=>starship F z i) _ ((contDiffAt_pi.mp (starship (G:=G) F|>.contDiff.contDiffAt (x:=0))) i)
    have hl : GradeAt 1 (reprc F K):= GradeAt.anchored (((show ContDiffAt ℝ ω (loop P ∘ represent) ((uniting F 0).2) from by rw [map_zero]; exact loop_smooth (m:=f) _ _ H).comp (f:=fun z:T=>(uniting F z).2) (0:T) (uniting F|>.contDiff.contDiffAt.snd)).sub (hc.log (by rw [h0];simp))) (by change loop P _-Real.log (J 0)=0; rw [h0,unitOpen,loop_origin _ _ H,Real.log_one,sub_zero])
    have hz : GradeAt 2 (Bulk.pillar (F:=F) (G:=G)):= GradeAt.shifts _ (show ContDiffAt ℝ ω (fun z:T=>z.1) 0 from contDiffAt_fst) rfl 2
    have hc : ContDiffAt ℝ ω (baseRatio F C (G:=G)) 0 := ((C.smooth.pow 2).inv (by simp [C.origin])).comp (f:=Prod.fst) (0:T) contDiffAt_fst
    have he : GradeAt 1 (fun z:T=> baseRatio F C z-1):= GradeAt.anchored (hc.sub contDiffAt_const) (by unfold baseRatio; simp [C.origin])
    exact ((he.mul (no_shift K F w B h)).add (hz.mul hl)).add ((GradeAt.unchecked hc).mul hp)
lemma matured (hW: Well W) : GradeAt 2 (core K F w C W):= (no_shift K F w B h).add ((home_adorn K F w C W B h hW).lower (by omega))
omit h
lemma born_mark (hW:Well W)(j:Hot R): GradeAt (W.power j) (scoreMark F C W j) :=by
   have he:= ((C.smooth.pow (W.power j)).inv (by simp [C.origin])).comp (f:=(Prod.fst: T→ℝ)) (0:T) contDiffAt_fst
   convert ((GradeAt.unchecked he).scale (hW.suppose_mark j |>.coarse (g:=fun z:T=> (ρ z.1,(uniting F z).2)) ((C.here.comp (f:=Prod.fst) (0:T) contDiffAt_fst).prodMk (uniting F|>.contDiff.contDiffAt.snd)) (by rw [map_zero,Prod.fst_zero,C.borne]; rfl) )) using 1 <;> first| rfl|omega
include h
lemma scored (hW : Well W) (x:X) (v:L): Assembly.jet (core K F w C W) 2 (translated K F x v)=Bulk.infrared S p P F w (K.b F) x + force (K.covariance F w) v/2 :=by
   let z:= translated K F x v; have ht:=(home_adorn K F w C W B h hW);
   have he := (binding K F w B h z).trans (K.force_square F w x v)
   rw [← he]; change Assembly.jet (fineScore F w K + adorn K F w C W) 2 z=_; unfold Assembly.jet; rw [iteratedFDeriv_add_apply ( (fineHome K F w).of_le le_top) (ht.smooth.of_le le_top),ht.vanish 2 (by omega), add_zero]

end YM.Comparison.RG02.FVAAlt2.Aperture
