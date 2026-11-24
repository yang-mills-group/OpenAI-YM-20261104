import YM.OPE.Compatible.Mould.Nave
/-!
# roots sect Λ cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} (D₀:Stern K P τ l d w)(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
open Flume.Script Maxwell Balsam Nestle Pert.Full Variance
-- Top templ.Life
structure SprigT (Q:Tracts G d τ)(r:Fin (e+1))(x: Bead G l e):Prop where
       top : (tag D₀ e Q) r=x r
       cap : Crop (r.val+1) Q
       veil (u:ℕ)(_hx:u<e): LimitQ (tag D₀ u Q) r.val
lemma Pollen (r:Fin (e+1))(he:e<l+1)(ht:r.val*l ≤ τ 0)(P:Tracts G d τ)(Q:Train k)(hq:4≤ k)(x:Bead G l e)(hp:Keeps (Fallix G D₀.aware K Q hq P) r.val (e-r.val) (fun v:Alphabet G l=>(impress x r).val (fun _=>v))): SprigT D₀ P r x:=by
       let T:=Fallix G D₀.aware K Q hq P; have hU(i)(hi:r.val≤ i) := leaderX hq Q D₀.aware P hp.cap hi; have h: Crop (r.val+1) P := fun i hi=>(hU i (Nat.le_trans (Nat.le_succ _) hi)).trans (hp.cap i hi)
       have hs:= sternCap D₀ 0; let y(i):= terrace G (d+(0:Phase).val) (τ 0) i (P 0); let Z':= Flume.Script.tiller G r.val (τ 0) (e-r.val) (by omega) l; have he':(y r.val).val = topX T r.val:= hU _ le_rfl -- paren
       obtain ⟨hB,hT⟩:= Bells_crit (y r.val) ht (show e - r.val < τ 0 from by omega) (by omega:l≥e-r.val) _ (show ∀ v, Tendsto (fun i:ℝ=>(i^(e-r.val))⁻¹* Lug ((y r.val).val) v i) (𝓝[>] 0) (𝓝 ((impress x r).val (fun _=> v))) from fun v=> (by rw [he']; exact hp.cue v))
       refine ⟨?_,h,?_⟩
       · rw [tagX D₀ P he]; rw [show Z' (y r.val)= _ from (show Z' (y r.val)=impress x r from prismInject _ _ hT)]; exact (coordinateQ G l e r.val).apply_symm_apply _
       intro u hu j hj; by_cases ht': j.val=r.val; swap; · exact (fringP D₀ P (by omega: u < l+1) h) j (by omega)
       obtain ⟨r,hr⟩:= r; obtain ⟨j,hj'⟩:=j; change j=r at ht'; subst j; dsimp only at hB ⊢ -- hz?
       let q:=y r; let C:=Flume.Script.tiller G r (τ 0) (u-r) (by omega) l; rw [tagX D₀ P (by omega)]; change coordinateQ _ _ _ _ (C q)=0; suffices he:C q=0 by rw [he,map_zero]
       apply Subtype.ext; apply (roll_inject q.val (patent_till q) (show u-r< τ 0 by omega) (show u-r≤l by omega) (patent q).2.1 (trimBell hB (show u-r ≤ e-r by omega))).2; exact trimBell hB (by omega)
-- Cost lemma
variable {t:M→ℝ}
lemma Zcost (p:M→E) [NormedAddCommGroup E](c:ℝ)(hc:0 ≤ c)(hv:1 ≤ t)(h:∀ i,‖p i‖ ≤ c*(1+t i)): Wealth p t 1:= by
     refine ⟨(2*c),by positivity,1,fun i=>?_⟩; rw [Pi.one_apply,pow_one,mul_one]; have hs:1 ≤ t i:=hv i; apply (h i).trans; nlinarith
lemma segmentWe [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{v:M→E}{C:M→ E→L[ℝ] F}{g:M→ℝ}(hx:Wealth C t 1)(hp:Wealth v t g):Wealth (fun i=> C i (v i)) t g:= one_mul g ▸ wealth_mul hx hp (fun i=>(C i).le_opNorm _)
end YM.OPE.Stroke
