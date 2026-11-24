import YM.X.Scheme.Table
import YM.X.Jet.Pale
/-!
`Lens n` finite-dimensional ledgers for one profile over any columns. Bank
use and Detectors reduce to these coordinate reads. Any pull (not varying profile)
is polynomial on ledgers.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Function Filter Set Pert Pert.Position
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (F:Labels.Frames G) {d n : ℕ}
local notation "W" => E F d
local notation "L"=> Buffer F d
abbrev Lens (d n:ℕ):=(Fin n→ ChartIx F d)→ℂ
def expose {d n:ℕ}(t:Test n) : Bank F d →ₗ[ℝ] Lens F d n where
   toFun w p:= w n t (baring F d ∘ p)
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
def emerge {d n : ℕ}(q: Lens F d n):MultilinearMap ℂ (fun _ : Fin n=>E F d) ℂ:= Bare.spread (baring F d) q
lemma reads_emerge (q:Lens F d n)(p): emerge F q (baring F d ∘ p)=q p := Bare.spread_eval ..
lemma regain (w:Bank F d)(t: Test n) : emerge F (expose F t w)=w n t:= Module.Basis.ext_multilinear (fun _=>baring F d) (fun p=>reads_emerge ..) -- function binder ..?
lemma expose_leg {X:Type*}{l: Filter X}{w:X→Bank F d}{v:Bank F d}(h:∀ s: Section F d,Tendsto (fun x=> lookie F s (w x)) l (𝓝 (lookie F s v)))(t:Test n) : Tendsto (fun x=> expose F t (w x)) l (𝓝 (expose F t v)):= tendsto_pi_nhds.mpr fun p=> h ⟨n,baring F d ∘ p,t⟩

def frameC {d}(b:Buffer F d) : Module.End ℂ (E F d) := LinearMap.id+ bufferL F b
lemma frameC_motor (b:L)(p:W): frameC F b p=motor F b p:= rfl
lemma frameC_zero {d}: frameC F (0:Buffer F d)=LinearMap.id:= LinearMap.ext (fun v=> add_zero _)
lemma frameC_par (b:L)(p:W): frameC F (cPar F b) p=par F d (frameC F b (par F d p)):= by unfold frameC; simp only [LinearMap.add_apply,map_add,bufferL_eq,LinearMap.id_apply,cPar_eq,par_cycle]
lemma frameC_up (b:L) {e:ℕ}(h:e≤d) (p:E F e): up F h (frameC F (zoomL F h b) p)= frameC F b (up F h p):= by unfold frameC; simp only [LinearMap.add_apply,map_add,LinearMap.id_apply,bufferL_eq,zoomL_eq]

def market {d}(b:Buffer F d)(w:Bank F d) := pulls (frameC F b) w
lemma market_proj (b:L)(w:Bank F d){e:ℕ}(h:e≤d): pulls (up F h) (market F b w)=market F (zoomL F h b) (pulls (up F h) w):= by
   unfold market; rw [pulls_join,pulls_join]; exact congr_arg (fun t=>pulls t w) (Eq.symm (LinearMap.ext (frameC_up F b h)))
lemma market_par (b:L)(v:Bank F d): market F (cPar F b) (pulls (par F d) v)= pulls (par F d) (market F b v):= by
   unfold market; rw [pulls_join,pulls_join]; apply congr_arg (fun t=> pulls t v); apply LinearMap.ext; intro p; rw [LinearMap.comp_apply,LinearMap.comp_apply,frameC_par,par_cycle]
lemma market_zero (v:Bank F d): market F 0 v=v:= by unfold market; rw [frameC_zero]; rfl

def cross (F:Labels.Frames G){d n : ℕ}(p:Fin n→ E F d)(x:Lens F d n × Buffer F d):= emerge F x.1 (frameC F x.2 ∘ p)
lemma cross_market (t:Test n)(p:Fin n→W)(v:Bank F d)(b:L):cross F p (expose F t v,b)=market F b v n t p:= by unfold cross; rw [regain];rfl
lemma cross_smooth (p:Fin n→ W): ContDiff ℝ ω (cross F p):= by
   unfold cross emerge; simp_rw [Bare.spread_value]; apply ContDiff.sum; intro i hi
   apply ContDiff.mul (contDiff_prod (fun k _=>?_))
   · exact (contDiff_apply ℝ _ _).comp contDiff_fst
   simp_rw [comp_apply,frameC_motor]; exact (((baring F d).coord (i k) |>.restrictScalars ℝ |>.toContinuousLinearMap).contDiff.comp (f:=fun w:Lens F d n × Buffer F d => motor F w.2 (p k)) ((motor_diff _).comp (f:=Prod.snd) contDiff_snd))
lemma cross_leaves (s: Section F d)(b:L)(w:Bank F d) : lookie F s (market F b w)=cross F s.p (expose F s.f w,b):= (cross_market ..).symm

-- finite representation preserves zoom via lin combos. Build noncomputable Ledger chosen finite via Finsupp.total
structure Rail {G:Gauge} (F:Labels.Frames G)(d:ℕ) where
   reached : Finset (Pert.Position.Section F d × Buffer F d)
   move (i:{x//x∈reached}): ℝ

variable {F}
namespace Rail
variable (R:Rail F d)
local instance appl : IsZeroApply (Bank F d→ₗ[ℝ] Buffer F d) (Bank F d) (Buffer F d):= by constructor; intro; rfl
local instance ap : IsAddApply (Bank F d →ₗ[ℝ] Buffer F d) (Bank F d) (Buffer F d):= by constructor; intros; rfl

def ofInterest (R: Rail F d): Bank F d→ₗ[ℝ] Buffer F d:= ∑ i:R.reached,R.move i • (project F i.val.1).smulRight i.val.2
lemma runs (D:Detector F d): ∃ (R:Rail F d), R.ofInterest=D.D:= by
   obtain ⟨c,hc⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp (show D.D∈Submodule.span ℝ _ from D.finiteD)
   exact ⟨⟨c.support,fun i=> c i.val⟩, (Finset.sum_coe_sort ..).trans hc⟩ -- name

def surveyor (D: Detector F d): Rail F d:= (runs D).choose
abbrev reachedV (i:R.reached) := i.val.1
abbrev Target := (i:R.reached) → Lens F d i.val.1.r

def common (R: Rail F d) : Bank F d →ₗ[ℝ] Target R:= LinearMap.pi fun i=>expose F (reachedV R i).f
def tableMap (R:Rail F d)(v:Target R × Buffer F d): Buffer F d:= ∑ i:R.reached,R.move i • Complex.re (cross F (reachedV R i).p (v.1 i,v.2)) • i.val.2
lemma atMarket (v:Bank F d)(b: Buffer F d): R.ofInterest (market F b v)= tableMap R (common R v,b):= by unfold ofInterest; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [LinearMap.smul_apply,LinearMap.smulRight_apply]; change R.move i • Complex.re (lookie F _ _) • i.val.2= _; rw [cross_leaves]; rfl
lemma common_limit {X:Type*}{l: Filter X}{w:X→Bank F d}{v:Bank F d}(h : ∀ s: Section F d,Tendsto (fun x=> lookie F s (w x)) l (𝓝 (lookie F s v))): Tendsto (common R ∘ w) l (𝓝 (common R v)) := tendsto_pi_nhds.mpr fun i=> expose_leg F h (reachedV R i).f
lemma tableMap_smooth : ContDiff ℝ ω (tableMap R):= by
   unfold tableMap; refine ContDiff.sum fun i _=>?_ ; let p:= (reachedV R i).p; let a (v: Target R × Buffer F d) := Complex.re (cross F p (v.1 i,v.2)); have h:ContDiff ℝ ω a:= Complex.reCLM.contDiff.comp (f:=fun v:Target R × Buffer F d => cross F p (v.1 i,v.2)) ((cross_smooth F p).comp (f:=fun v:Target R × Buffer F d=>(v.1 i,v.2)) (by
       let Z : R.Target × Buffer F d →ₗ[ℝ] Lens F d (reachedV R i).r × Buffer F d:= ((LinearMap.proj i) ∘ₗ LinearMap.fst ℝ _ _) |>.prod (LinearMap.snd ℝ _ _); exact ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=R.Target × Buffer F d) (F:=Lens F d (reachedV R i).r × Buffer F d) (LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=R.Target × Buffer F d) (F':=Lens F d (reachedV R i).r × Buffer F d) Z)))
   have he : ContDiff ℝ ω (fun v:Target R × Buffer F d=> a v • i.val.2):= by exact ContDiff.smul h contDiff_const
   exact ContDiff.const_smul (R.move i) he
end Rail
end YM.PositionX
