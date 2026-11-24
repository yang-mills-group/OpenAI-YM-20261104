import YM.OPE.Compatible.Dent.Copse
/-!
# Combined Pact. Costs in step units only. k ≤ B. Horizon sup conservatively hardcoded 100.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset WilsonStartup
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ C w ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
section
variable {J:Seats F}{X Y:Support f}
lemma tweaktribes {u v:Config G f→ℝ}: tweak J (u+v) = tweak J u+tweak J v:=funext fun i=>by simp [tweak];ring
lemma tweakYaw {u:Config G f→ℝ}{a:ℝ}: tweak J (a • u) = a • tweak J u:=funext fun i=>by simp [tweak];ring
-- Boot purely. Array with ECG path.
def groupsV (R:Rep G f) (l l' l₃ l₄: Config G f→ℝ):= (R.beta • (l+l₃+l₄))+l'
def smoke (R:Rep G f)(s:Signed)(i:ℕ) := groupsV R ((acid R).lathe s i) ((emberY R R.path.loop).lathe s i) ((emberY R R.path.cubic).lathe s i) ((emberY R R.path.quartic).lathe s i)
def brim (R:Rep G f)(s:Signed)(i:ℕ) := groupsV R ((acid R).lobe s i) ((emberY R R.path.loop).lobe s i) ((emberY R R.path.cubic).lobe s i) ((emberY R R.path.quartic).lobe s i)
def copeV (R:Rep G f)(s:Signed)(i:ℕ) := groupsV R ((acid R).honey s i) ((emberY R R.path.loop).honey s i) ((emberY R R.path.cubic).honey s i) ((emberY R R.path.quartic).honey s i)
def burn (R:Rep G f)(X:Support f)(u e a δ ε:ℝ) (l:ℕ):= 2*(X.card*(est R.p ε * (Real.exp (R.p.supportExponent*a-u/2*l)*e))) + δ*0 -- edit
open Geo
-- G implicit
def marksV (R:Rep G f)(X:Support f)(σ ε C Λ:ℝ)(l:ℕ):= let A:= burn R X (3*σ/4) ((2*R.p.threshold)*lowerSize R.clip C) lowCount 0 ε l
      let T (d:ℕ) (a:ℝ):= burn R X σ (2^d*a) (1+d*2) 0 ε l
      ‖R.beta‖*(A+T 3 C+ T 4 C)+T 2 Λ
variable (J)(h:R.Lawful σ C Λ E w)(hc:Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ) (F':FoldsGrip F J X)
include h hc hy
lemma reunited (s:Signed)(i:ℕ)(U:Config G f): smoke R s i U + brim R s i U= R.path.principal R.clip R.p R.beta (pull s 0 U):=by
   obtain ⟨_,ha⟩:= acidic hc h hy; let V:= pull s 0 U; have hA := ha.orthoSum (by linarith [h.paths.width]) s i U
   rw [show (∑ x:Site f,∑' j, (acid R).moon s (x,j) U)=∑ b:Face (Per f),R.path.baseTerm R.clip R.p V b from ?_] at hA; swap; · rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i hi=>?_ ; exact Low.live_total h.paths hy i _
   have hz(d:ℕ)(Z:ℕ→ Atom G d)(e:ℝ)(hp:SumBudget (fun i=>(Z i).budget σ) e)(hg:∀ i,(Z i).Invariant):
        let A:=emberY R Z; A.lathe s i U+A.lobe s i U= ∑ x:Site f, PathData.atomSeries Z R.p V x:= by intro A; obtain ⟨_,hS⟩:= soundsE (R:=R) Z hg hp; exact hS.orthoSum h.paths.width.le s i U
   let v:=R.path.principal R.clip R.p R.beta V
   have hf:= hz 2 _ _ h.paths.two (fun i=>(h.paths.invariant _).1); have hv:= hz 3 _ _ h.paths.three (fun i=>(h.paths.invariant _).2.1); have hx:= hz 4 _ _ h.paths.four (fun i=>(h.paths.invariant _).2.2)
   change _=v; unfold v PathData.principal; rw [Finset.sum_add_distrib,←hA,←hf,←hv,←hx]; unfold smoke brim groupsV; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
include F' in
lemma nutrient (ha:t+ε ≤ R.p.supportExponent)(hε:0<ε)(hp:0≤t)(hs:2*R.p.supportExponent ≤ R.p.B*(3*σ/4))(l:ℕ)(s:Signed): Sable R S X t (tweak J (smoke R s l)) (marksV R X σ ε C Λ l):= by
   obtain ⟨_,hF⟩:= acidic hc h hy; have h' (d:ℕ)(Z:ℕ→ Atom G d)(C:ℝ)(hv:SumBudget (fun i=>(Z i).budget σ) C)(hk:∀ i,(Z i).Invariant): Sable R S X t (tweak J ((emberY R Z).lathe s l)) (burn R X σ (2^d*C) (1+d*2) 0 ε l):=by
     obtain ⟨_,hS⟩:= soundsE (R:=R) Z hk hv; unfold burn; rw [mul_zero,add_zero]; exact hS.lit_budget s F' ha hε hp h.paths.width (hs.trans (mul_le_mul_of_nonneg_left (by linarith [h.paths.width]) (by positivity))) _
   have ht: Sable R S X t (tweak J ((acid R).lathe s l)) (burn R X (3*σ/4) ((2*R.p.threshold)*lowerSize R.clip C) lowCount 0 ε l):=by
        unfold burn; rw [mul_zero,add_zero]; exact hF.lit_budget s F' ha hε hp (by linarith [h.paths.width]) hs l
   unfold smoke groupsV; rw [tweaktribes, tweakYaw,tweaktribes,tweaktribes]
   exact (((ht.addition (h' _ _ _ h.paths.three (fun i=>(h.paths.invariant i).2.1)) hp).addition (h' _ _ _ h.paths.four (fun i=>(h.paths.invariant i).2.2)) hp).scale R.beta).addition (h' _ _ _ h.paths.two (fun i=>(h.paths.invariant i).1)) hp
end
end YM.PhysicalNext.Repeat.Aroma
