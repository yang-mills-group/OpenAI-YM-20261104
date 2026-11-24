import YM.Comparison.RG02.Adjacent.Compatibility
/-!
# Re-expression of local WilsonX Fk in its chosen output coupling scheme

Products through order r now use `adj.Fk` in the new parameter (`Integral.K.charge` still in
current actual one). Keep the zeroth thermal quadratic factor outside when exponentiating and its
adjustment `known` on the new path. Don't recompute masks/log labels just from these identities.
Includes orientation etc only of series, contiguous with previous Sheet readouts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {c f:Side} {S:StepData c f} {p:Clip}{P:PathData G}{O:ChartRatio G}
    (K:Bulk.Kernel S p P O) (D:BudgetPoint)(F:Forest S.ratio)(w:S.Choices)
    (d:V→ℤ) (W:Bulk.Colors R G f)(T:UnitCost)(C:Caliber)
    (s:R.Mode)(r:ℕ)(x:fieldDir G c 1)
namespace LocalScript
open Cumulants
open Trade (markDebt)
local notation "X"=> fieldDir G c 1
local notation "Γ" u=> Bulk.Fk K F w W u r
local notation "U"=> ground K F w W r
local notation "σ"=> price K F w
local notation "A"=> words K F w W r
local notation "ρ"=> T.rating
-- caller will use `C.back r` not `C.direct` for next-to-coarse.
def costPrice := fun t=> price K F w ((T.rating t)⁻¹ • x)
def signal : fieldDir G c 1→ Grade R r:= Trade.barter T d r (fun u=> Γ u)
lemma accounts : Trade.Shows r (fun u=> Γ u):= Trade.Shows.knows r (fun _=>Bulk.fk_sym ..) (fun i=> moments_smooth K F w W r i) fun _=> Bulk.fk_unit ..
lemma reads : UnitLeading (signal K F w d W T r x) ∧ Order.Symmetric (signal K F w d W T r x) := ⟨(accounts K F w W r).rolls T d r x,(accounts K F w W r).sees T d r x⟩
lemma recount (i:ℕ)(hi:i≤r): detail (logMarked (signal K F w d W T r x)) s i=born (words K F w W r s) T (markDebt d s) r i x:= (accounts K F w W r).utter T d r s x i hi
lemma flare (i:ℕ)(hi:i≤r): motion (costPrice K F w T x) i + detail (logVac (signal K F w d W T r x)) R.quiet i=born (ground K F w W r) T 0 r i x:= by
   let L:= Trade.read r (logVac ∘ (fun u=> Γ u)) R.quiet; have hv(t): cover U r (T.enter t) ((T.rating t)⁻¹ • x)=costPrice K F w T x t + cover L r (T.enter t) ((T.rating t)⁻¹ • x) :=by
      let y:= (T.rating t)⁻¹ • x; unfold cover ground costPrice; rw [add_comm (σ _),show (∑ j∈_,_)= (∑ i∈range (r+1), (T.enter t:ℂ)^i*L i y)+(∑ i∈range (r+1), (T.enter t:ℂ)^i* (if i=0 then σ y else 0)) from by simp_rw [mul_add,sum_add_distrib]; rfl]; simp [y]
   unfold signal; rw [(show detail _ _ _= _ from (accounts K F w W r).read_cost T d r x i hi)]
   have hb : Charge r (fun i=> ↑(i+2 : ℕ)) L:= fun i _=> vacuum_read K F w W r i
   have hx: ContDiffAt ℝ ω (fun t:ℝ=> (T.rating t)⁻¹ • x) 0:= ((T.smooth.inv (by simp [T.origin])).smul contDiffAt_const)
   have hu : (fun t:ℝ=> ages L 0 r t (T.rating t) x)= fun t=> cover L r (T.enter t) ((T.rating t)⁻¹ • x):= by unfold UnitCost.enter ages; simp
   have he (t:ℝ): ages U (0:ℤ) r t (T.rating t) x=costPrice K F w T x t + ages L (0:ℤ) r t (T.rating t) x:= by rw [congrFun hu t]; unfold ages; simpa [UnitCost.enter] using hv t
   change _ + motion (fun t=> ages L 0 r t (T.rating t) x) i= _; rw [born, _root_.funext he]; exact (Moving.Shift.madd ((price_ready K F w).contDiffAt.comp _ hx) (hu.symm ▸ buying r hb T _ hx)).symm

-- pricing & parity on the ranks
lemma levy_rank (q:ℝ) : price K F w (q • x)=q^2 • price K F w x:= by
   let V:X→L[ℝ]Bulk.SliceDir S F G:= (ContinuousLinearMap.id ℝ _).prod (fderiv ℝ (K.b F) 0)
   unfold price Bulk.infrared; rw [show Bulk.classical S F (K.b F) (q•x)= q • Bulk.classical S F (K.b F) x from V.map_smul q x, Assembly.Clipper.weight]; simp [smul_eq_mul,Complex.real_smul]
lemma precedence : ground K F w W r 0 x=price K F w x:= by
   change Second.lit 0 (logVac (Γ x)) + _ = _; rw [Order.Second.leading]; rw [logVac,denominator, Extra.Trajectories.connected_quiet ((bottom_quiet (Γ x)).trans (Bulk.fk_unit ..)),zero_add,if_pos rfl]
lemma here (n:ℕ) : Assembly.jet (price K F w) n x= if n=2 then price K F w x else 0:= by
   apply congrFun ((Ranking.impression (price_ready K F w|>.contDiffAt) x).unique ?_) n
   simp_rw [levy_rank]; exact Aspiration.single _ _
lemma tax_p : Level 2 (price K F w):= by
   have hx: Assembly.jet (price K F w) 2=(price K F w):= funext fun x=> (here K F w x 2).trans (if_pos rfl)
   have hh:= levelJet (price_ready K F w|>.contDiffAt) 2; rw [hx] at hh; exact hh
lemma rank : Charge r (fun i=> (↑i+2:ℤ)) (ground K F w W r):= by
    intro i _; by_cases hi:i=0
    · subst i; rw [show ground _ _ _ W r _= _ from funext (precedence K F w W r)]; simpa using tax_p K F w
    simp_rw [show ground K F w W r i=(fun u=> detail (logVac (Γ u)) R.quiet i) from funext fun u=>by simp [ground,hi]]; exact_mod_cast (vacuum_read K F w W r i)
lemma marked_rank (σ':V→ℤ)(h : Toile W.power s σ'): Charge r (fun i=> (↑i+2+(∑ v∈s.val,σ' v):ℤ)) (words K F w W r s):= fun i _=> mark_read K F w W σ' s i h
lemma real : Rim (ground K F w W r 0 x) := by rw [precedence]; exact (Rim.ofReal _).neg
lemma gesture (i:ℕ)(hi : i≤r): Rim (ground K F w W r i x) := by
    by_cases hx:i=0; subst i; exact real ..
    unfold ground detail observe; rw [if_pos hi, if_neg hx, add_zero]
    let L:= logVac (Γ x); change Rim ((i.factorial:ℂ)⁻¹ * L.part _)
    apply (Rim.natural i.factorial).inv.mul
    have H(t):= log_color (Γ x) (Bulk.uncolored K F w W x r) (Bulk.fk_unit ..) t
    unfold denominator at H; rw [log_vacant (Bulk.fk_unit ..)] at H; exact H _
lemma signals (i:ℕ): Rim (born U T 0 r i x) := Preserves.stays 0 T (fun i he=> ((rank K F w W r i he)).smooth) (fun i he x=> gesture K F w W r x i he) i x

variable (hW:Bulk.Well W)
include hW
lemma seals (h: T.Even) (he: Mirror.Calm W): Preserves.Weight (born U T 0 r) r 1 := by
   refine Preserves.retained 0 h ?_ (fun i _=> smooth_ground ..); intro i hi x; by_cases H:i=0
   · subst i; rw [precedence,precedence,pow_zero,mul_one,one_mul, ← neg_one_smul ℝ x,levy_rank,neg_one_sq,one_smul]
   unfold ground; have hx:= Valence.Parity.even_vac K F w W r hW i he x; rw [if_neg H,add_zero,if_neg H,add_zero,one_mul]; simpa only [detail,Mirror.shape, Census.quiet,prod_empty,mul_one] using hx
lemma known (h:T.Even)(g:V→ℂ)(he: Mirror.Sound W g): Preserves.Weight (born (words K F w W r s) T (markDebt d s) r) r (∏ i∈s.val,g i):= by
   refine Preserves.retained (markDebt d s) h ?_ fun i _=> (mark_read K F w W _ s i (every W.power s)).smooth; intro i hi v; rw [mul_comm (∏ _i∈_,_)]; exact Valence.Parity.mark K F w W g r s hW i he v
include D
lemma stays : Sheet r (born (ground K F w W r) T 0 r):= Call.certified 0 r (rank K F w W r) T (bed K D F w W r hW)
lemma shady : Sheet r (born (words K F w W r s) T (markDebt d s) r):= Call.certified (markDebt d s) r (marked_rank K F w W s r _ (every W.power s)) T (colored K D F w W r s hW)
lemma winter (t : Signed)(b:Site c)(h:∀y,W.vac y ∘ pull t (S.ratio.embed b)=W.vac y)(i:ℕ): (born U T 0 r i) ∘ AnalyticNext.QuarticMatch.Joint.shifts t b = born U T 0 r i := Adjacent.point 0 r _ (fun i _=> Pole.season K D F w t b r hW h i) T i
end LocalScript
end YM.Comparison.RG02.Adjacent
