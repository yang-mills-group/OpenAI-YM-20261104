import YM.FVAAlt2.Booth.Clock
/-! # Assemble the periodic $Vacuum.inputs receipts. Matter. Price.t in term, reached from cover primitives. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth.Gala
open Function Finset MeasureTheory Filter Set Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Deck Motion Prim PertExtension Series Series.Radial Series.Tested Chart Lattice Tree Gauge Binding Diagram Diagram.Formal RG Wilson Oracle Geometry
open PowerSeries Exterior Precision Bid Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix Matrix.Norms.Frobenius
variable {c f n:Side}{G:Gauge}{p: RG.Clip}{O:ChartRatio G}{U:PathData G}
variable (S:StepData c f)(F:Forest S.ratio) (L: Binding.Scale) (H:S.patch.Branches S.kernel G)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=> Comparison.RG02.Bulk.Joint S F (G:=G)
local notation "Q"=>Pins f c G

variable {V:Type} [DecidableEq V] {R:Marker.Census V}
variable (W:Bulk.Colors R G f)(K: Comparison.RG02.Bulk.Kernel S p U O)(C:UnitCost) (w:Geometry.Field.Square F)
open Tape
local notation "τ"=> Ribbon.fees C
local notation "χ"=> C.enter
local notation "J"=> directive S
local notation "g₁"=> Aperture.core K F (directive S) C W

def feeAct (p:RG.Clip)(U:PathData G)(C:UnitCost)(W:Colors R G f)(x':fieldDir G f 1)(t:ℝ):ℝ:= Ribbon.fees C t*( mainTerm p U ( sample t x') + W.vac (C.enter t) (sample t x') ) + t^2*Precision.loop U (sample t x')
local notation "P"=> feeAct p U C W
variable (x:Comparison.RG02.Bulk.Joint S F (G:=G))
local notation "V₁"=> Aperture.uniting F x
local notation "q"=> Tape.announceT (Aperture.uniting F x)
local notation "φ"=>Tape.haunt S F K

def noise (x':Work.F03.Logs G c f)(t:ℝ):= noiseTaylor S (sample t x'.1) (sample t x'.2) (directive S)
local notation "p₀"=> noise S ( V₁ )
lemma charge0 (h:x.1=1)(t:ℝ): g₁ (t • x)= P (V₁).2 t + τ t * p₀ t - t^2 * φ t x:= by
    unfold Aperture.core Aperture.adorn Aperture.fineScore Aperture.freshvac Aperture.reprc Aperture.baseRatio Tape.haunt feeAct Aperture.opens noise pillar Work.F03.flat; unfold sample; simp only [ _root_.map_smul,show (t • x).1=t from (show t * x.1=t from by rw [h,mul_one]),show (t • (V₁)).2= t • (V₁).2 from rfl,show (t • (V₁)).1=t • (V₁).1 from rfl]; unfold Ribbon.fees; ring -- hope map_smul starship
-- analytic enough at uniform t.Recipe parameters ζ. (need Credit when other windows)
variable (hW:Well W)
include K hW
lemma active_pay (y:Y) : ContDiffAt ℝ ∞ (feeAct p U C W y) 0:= by
   obtain ⟨e,u,l,D'⟩:= K.bounds
   have h₁:= (Extra.Iteration.Calibration.main_jet (n:=f) D')
   let p'(t:ℝ):=t • y; have hv:p' 0=0:=zero_smul ..; have ht: ContDiffAt ℝ ω p' 0:=contDiffAt_id.smul contDiffAt_const
   have hPre : ContDiffAt ℝ ω (feeAct p U C W y) 0:= by
      unfold feeAct; apply (((Ribbon.ordered C).mul ( ContDiffAt.add ( show ContDiffAt ℝ ω ( mainTerm p U ∘ (represent (G:=G) (n:=f)) ∘ p' ) 0 from ((show ContDiffAt ℝ ω ( mainTerm p U ∘represent ) (p' 0) from hv.symm ▸ h₁).comp _ ht)) ?_ )).add ( (contDiffAt_id.pow 2).mul ((show ContDiffAt ℝ ω ( loop U ∘ represent ) (p' 0) from hv.symm ▸ loop_smooth (m:=f) _ _ D').comp (f:=p') (0:ℝ) ht)))
      exact ContDiffAt.comp (g:= Bulk.projected W.vac) (f:=fun t=> (χ t,p' t)) _ (by rw [hv,C.borne]; exact hW.suppose_vac.smooth) (C.here.prodMk ht)
   exact hPre.of_le le_top
omit hW
lemma noise_s (v: Work.F03.Logs G c f): ContDiffAt ℝ ω (noise S v) 0:=by
   obtain ⟨e,u,l,D'⟩:= K.bounds
   let p'(t:ℝ):=t • v
   have hz:p' 0=0:=zero_smul ..; let μ(z:Work.F03.Logs G c f):= Extra.Iteration.Calibration.main U p z.2; have hm : ContDiffAt ℝ ω μ 0:= (Extra.Iteration.Calibration.main_jet D').comp (f:=Prod.snd) (0:Work.F03.Logs G c f) contDiffAt_snd
   have ht : ContDiffAt ℝ ω ( Work.F03.flat S (directive S) p U - μ ) (p' 0) := hz.symm ▸ (( Work.F03.flat_smooth K.branches J (Work.F02.answer G p U e u l D') ).sub hm)
   apply (ht.comp (f:=p') (0:ℝ) (contDiffAt_id.smul contDiffAt_const)).congr_of_eventuallyEq; filter_upwards with i; change _=_+noise S v i - _; unfold μ Extra.Iteration.Calibration.main; abel -- change may object
lemma chute : ContDiffAt ℝ ∞ (fun t:ℝ=> Tape.haunt S F K t x) 0:=by
   let z(t:ℝ):=t • x; have ht : ContDiffAt ℝ ∞ z 0:= by exact contDiffAt_id.smul contDiffAt_const
   let J'(z:T):= ∏ i,O.J (Aperture.starship F z i); have he : ContDiffAt ℝ ∞ J' 0:= by
      refine contDiffAt_prod fun i _=> (show ContDiffAt ℝ ∞ O.J (Aperture.starship F 0 i) from ?_).comp (f:=fun z:T=> Aperture.starship F z i) 0 ((contDiffAt_pi.mp ( Aperture.starship F|>.contDiff.contDiffAt (n:=∞) (x:=(0:T)))) i)
      rw [map_zero]; exact (K.ratio.germ 0 ( Metric.mem_ball_self K.ratio.patch ) ).of_le le_top
   apply (show ContDiffAt ℝ ∞ J' (z 0) from (show z 0=0 from zero_smul ..).symm ▸ he ).comp (f:=z) _ ht|>.log; simp [z,J',K.ratio.anchored]

variable {r:ℕ} (h:Ribbon.Align r L C)
include h
lemma know_clock : Ward.Squares (r+2) (Prim.tale (L.beta*p₀)) (Prim.tale ( τ*p₀ )):=by
    have ht := (noise_s S K V₁).of_le (m:= ∞) le_top; rw [tale_mul L.near ht,tale_mul ((Ribbon.ordered C).of_le le_top) ht]; exact Clocks.movesV h (Clocks.grows_sq ht (fun _=> noise_pos ..) (by simp only [noise,sample,zero_smul,link_one]; exact noise_origin S J K.branches))

omit K h
variable {Z : Branchix→ Orders (KFoot G)} (Hv: Prim.Sphere S F L Z)
local notation "S'"=> studied Z f c
include K w Hv
lemma gain (e:ℕ)(he:0<e): coeff e ( flavor 2 q S' )= coeff e (Prim.tale (fun t=> φ t x)) - coeff (e+2) (Prim.tale (L.beta*p₀)) := by
   rw [aced Hv _ he,Fintype.sum_sum_type]; rw [← outcomesL S F L w K x, map_sum];
   have hR: Prim.tale (L.beta*p₀)=_:= (Tape.outcomesR S F L K.branches V₁).symm -- adjust
   rw [hR,map_sum ,sub_eq_add_neg,← Finset.sum_neg_distrib]; refine congr_arg₂ (fun x y:ℝ=>x+y) (sum_congr rfl (fun i _=>one_mul _)) (sum_congr rfl (fun i _=>neg_one_mul _))

-- positive joint basis at absolute trajectory before paying HO scale. price family P.Parameter.
variable (B:Bed)(hb:YM.FVAAlt2.Period.Rent.Right p U f B)
include h hW hb
lemma comm (e:ℕ)(h':0<e)(he:e≤r)(hx:x.1=1): Assembly.vacuumLetter g₁ x e = -(coeff (e+2) (Prim.tale (feeAct p U C W (V₁).2))) + coeff e ( flavor 2 q S' ) :=by
    rw [ Assembly.vacuumLetter, if_neg h'.ne',Assembly.jet_eq,gain S F L K w x Hv e h',know_clock S F L K C x h _ (by omega), ← show coeff (e+2) (inscription g₁ x) =_ from PowerSeries.coeff_mk ..,← lore ( (Aperture.matured K F J C W B hb hW).smooth.of_le le_top ) x ];
    let g:=noise S V₁; let Y':ℝ→ℝ:= fun t=> t^2; let Z' := fun t=>φ t x; let R' := Y'*Z'; let u:= feeAct p U C W (V₁).2
    have ht:=active_pay S W K C hW (V₁).2; have hp : ContDiffAt ℝ ∞ (τ * g) 0:= (Ribbon.ordered C|>.of_le le_top).mul ((noise_s S K V₁).of_le le_top); have hv : ContDiffAt ℝ ∞ Y' 0:= contDiffAt_id.pow _; have h₁:=chute S F K x; have hd:ContDiffAt ℝ ∞ R' 0:= hv.mul h₁
    rw [show (fun t:ℝ=>g₁ (t • x))= (u + (τ * g)) + -R' from funext (fun i=> charge0 S F W K C x hx i|>.trans (sub_eq_add_neg ..)), tale_add (f:=u+τ*g) (g:=-R') (ht.add hp) hd.neg, tale_add (f:=u) ht hp, tale_neg hd ]; simp only [map_add,map_neg];unfold R'; rw [tale_mul (g:=Z') hv h₁,Script.dictates (f:=Y') hv (Script.predicts_pow 2), PowerSeries.coeff_X_pow_mul ]; unfold g Z' u; abel
-- seed contracts.Spatial.Input fields rather than pretending compute.Mark.
end YM.RegulatorIR.FVAAlt2.Booth.Gala
