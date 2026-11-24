import YM.Comparison.RG02.Symmetry.Action
import YM.Comparison.RG02.Symmetry.Spring
import YM.Comparison.RG02.Laplace.Choice
/-!
# Rise of the rescaled Ward identity

 Near varying Ward paths in true group, before capture, keeping actual slice and tag. Condition
 measure relative scalar pad still charged at x₀. Proven not using real cost estimates, but
 with direct finite-period analytic argument. Stages and weights `Seen` paths have ξ their own
 (real), Fourier moment/cover/S resolution later by Task01/08 etc. No coefficient transfer
 through those operations claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Moving Moving.Path Moving.Shift Marker Multi Order YM.Next.SectorChange Integral Actual Laplace Valence
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (w : S.Choices)
  (a b : ℝ→fieldDir G c 1)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
  (W : Bulk.Colors R G f) (r : ℕ)
local notation "φ"=> 𝓝 (0:ℝ)
local notation "Ω" x=> Bulk.Fk K F w W x r
local notation "κ"=> pad K F w 0
local notation "σ"=> calorie K F w 0
local notation "ν"=> fuse R r
local notation "X"=> fieldDir G c 1
open YM.Extra.Trajectories (connected)
structure Flow (x y:ℝ→fieldDir G c 1) : Prop where
 bend : ∃ (u : G.El) (L : ℝ→ Site c→G.El), Tendsto L along (𝓝 fun _=>u) ∧
     ∀ᶠ t in along,sample t (x t)=gauge (L t) (sample t (y t))
-- orbit directional read
abbrev glows (a : ℝ→fieldDir G c 1) := ContDiffAt ℝ ω a 0
def raw (v : ℝ) := Ω(a v)
def pulse (t:ℝ) : ℂ:= κ (a t)

def price (x:X): ℂ:= -(Bulk.infrared S p P F w (K.b F) x:ℂ)
lemma price_ready : ContDiff ℝ ω (price K F w):= by
    let L:X→L[ℝ] Bulk.SliceDir S F G:= (ContinuousLinearMap.id ℝ _).prod (fderiv ℝ (K.b F) 0)
    let g: X→ℝ:= Bulk.infrared S p P F w (K.b F)
    have h: ContDiff ℝ ω g:= (Tensor.diag_smooth (Tensor.coeff (Bulk.Surface S p P F w) 2 0) ω).comp L.contDiff
    exact (Complex.ofRealCLM.contDiff.comp h).neg
private lemma pad_motion : ContDiff ℝ ω κ:= by
    let g: X→ℝ:= fun x=> -(price K F w x).re; have h: ContDiff ℝ ω g:= (Complex.reCLM.contDiff.comp (price_ready K F w)).neg; have hv : g= Bulk.infrared S p P F w (K.b F) := by ext x; simp [price,g];
    unfold pad calorie; rw [← hv]; exact (contDiff_const.mul (contDiff_const.mul ((contDiff_const.sub h).exp))).div_const _
lemma tax (x y:X) : κ x = Real.exp ((((price K F w x)-(price K F w y))).re)*(κ y):= by
   unfold price pad calorie; simp only [Complex.sub_re,Complex.neg_re,Complex.ofReal_re,zero_sub]; rw [Real.exp_sub]; field_simp


variable (hW : Bulk.Well W)
def lit (t:ℝ) := pulse K F w a t • raw K F w a W r t
lemma lit_value (t:ℝ)(s:R.Mode): (value (t:ℂ) (lit K F w a W r t)).part s=pulse K F w a t*(value (t:ℂ) (raw K F w a W r t)).part s:= by
   unfold lit
   rw [show value (t:ℂ) (_:Grade R r) = _ from map_smul (valueL R r (t:ℂ)) _ _, Poly.part_smul]; rfl
-- unfolds Ready along orbit; comprehensive valuation of f as power series implicit
variable (ha : glows a)
include ha
lemma seen_raw : Seen (raw K F w a W r):= ⟨fun i=> (moments_smooth K F w W r i).contDiffAt.comp (0:ℝ) ha⟩
lemma seen_pulse : ContDiffAt ℝ ω (pulse K F w a) 0 := (Complex.ofRealCLM.contDiff.comp (pad_motion K F w)).contDiffAt.comp (0:ℝ) ha
lemma seen_lit : Seen (lit K F w a W r):= by
   constructor; intro i; simp_rw [lit,Poly.part_smul]; exact (seen_pulse K F w a ha).mul ((seen_raw K F w a W r ha).smooth i)

omit ha
lemma ready_raw : ∀ᶠ t in φ,Order.Symmetric (raw K F w a W r t):= Eventually.of_forall fun t=> Bulk.fk_sym K F w W (a t) r
lemma leads_raw : ∀ᶠ t in φ,UnitLeading (raw K F w a W r t):= Eventually.of_forall fun t=> Bulk.fk_unit K F w W (a t) r
lemma ready_lit : ∀ᶠ t in φ,Order.Symmetric (lit K F w a W r t):= (ready_raw K F w a W r).mono fun _ ht=>ht.smul _
lemma stamp_lit : (ν (lit K F w a W r)).part ((Board R r).quiet)= pulse K F w a 0:= by
   rw [stamp0,lit,Poly.part_smul,show (raw K F w a W r 0).part ((Board R r).quiet)=1 from Bulk.fk_unit K F w W (a 0) r,mul_one]

include ha
lemma ledger (s:R.Mode) : ContDiffAt ℝ ω (fun t:ℝ=> (value (t:ℂ) (lit K F w a W r t)).part s) 0 := by
   simp_rw [vpart]; exact ContDiffAt.sum fun i _=> (Complex.ofRealCLM.contDiff.contDiffAt.pow i).mul (Moving.Shift.watch (seen_lit K F w a W r ha) s i)

local notation "Δ" s => detail (ν (lit K F w a W r)) s
include D hW
lemma demands (s:R.Mode) : ∃ B∈𝓝 (1:F.Slice G), IsOpen B ∧ ∀ A, Liberty F A B→ Trial (Δ s) (fun t=> pulse K F w a t*(portal K F w 0 W (a t) A t).part s) r := by
   have ht: Tendsto a along (𝓝 (a 0)):= ha.continuousAt.mono_left (show along≤φ from nhdsWithin_le_nhds)
   obtain ⟨B,HB,hB,H⟩:= accost K D F w (a 0) a W 0 r s hW ht; refine ⟨B,HB,hB,fun A hv=>?_⟩
   let f(t:ℝ):= (value (t:ℂ) (lit K F w a W r t)).part s
   let g(t:ℝ):= (value (t:ℂ) (raw K F w a W r t)).part s
   let p(t:ℝ):= (portal K F w 0 W (a t) A t).part s
   let e:= pulse K F w a
   have hf : Trial (Δ s) f r:= trial_flow (a:=Moving.Path.motion f) (Moving.Path.ordinary ((ledger K F w a W r ha s).of_le le_top) r) (fun i hi=> Moving.Shift.valued (seen_lit K F w a W r ha) (ready_lit K F w a W r) hi)
   have hh:= bill_mul (Moving.Path.ordinary ((seen_pulse K F w a ha).of_le le_top)|>.bounded) (H A hv)
   rw [Nat.zero_add] at hh
   change Bill _ (e*(p-g)) at hh
   change Trial _ (e*p) _; unfold Trial; rw [show e*p-peval _ r=e*(p-g) + (f-peval (Δ s) r) by rw [show f=e*g from funext fun i=> lit_value K F w a W r i s]; ring]; exact bill_add hh hf
variable (hb : glows b) (H : Flow a b)
include hb H
-- deliver Ward as exact identity incl scalar and ratio root. Need no symmetry assume n even.
lemma balances : ν (lit K F w a W r)=ν (lit K F w b W r):= by
   rcases H with ⟨u,L,hs,h⟩ -- fields shape
   apply (sym_coeff _ _ (fuse_symmetric (ready_lit K F w a W r)) (fuse_symmetric (ready_lit K F w b W r))).2; intro k hk; ext s
   obtain ⟨A,hA,hi,HP⟩:= demands K D F w a W r hW ha s; obtain ⟨B,hB,hx,HQ⟩:=demands K D F w b W r hW hb s
   obtain ⟨U,V,hU,hV,he⟩:= Switch.law F hB hA hx hi u L hs
   refine trial_gap (trial_congr ?_ (HP V hV)) (HQ U hU) k hk
   filter_upwards [eventually_pos,h] with t ht hz
   have hy : Complex.ofReal (wage K F w t 0 (a t)) • portal K F w 0 W (a t) V t=Complex.ofReal (wage K F w t 0 (b t)) • portal K F w 0 W (b t) U t := by
      have ht(x:X): (Complex.ofReal (wage K F w t 0 x))≠0:= by exact_mod_cast (wage_pos K F w t 0 x ht).ne'
      unfold portal; rw [smul_smul,smul_smul,mul_inv_cancel₀ (ht (a t)),mul_inv_cancel₀ (ht (b t)),one_smul,one_smul,hz,he]; exact Switch.backswitch F w (L t) (model t 0 W K) _ _ _ K.branches (model_gauge K t 0 W hW)
   rw [wages K F w t 0 (a t) ht,wages K F w t 0 (b t) ht,Complex.ofReal_mul,Complex.ofReal_mul] at hy
   apply mul_left_cancel₀ (show (Complex.ofReal (common S t F G)) ≠0 from Complex.ofReal_ne_zero.mpr (common_free F t ht (G:=G) |>.ne')); unfold pulse; rw [← mul_assoc,← mul_assoc]; exact congrArg (Poly.part · s) hy
end YM.Comparison.RG02.Symmetry
