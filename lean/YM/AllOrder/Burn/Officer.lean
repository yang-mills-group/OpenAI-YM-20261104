import YM.AllOrder.Burn.Mettle
import YM.AllOrder.Burn.Revenue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer

/-!
F4: port of YM.AllOrder.High.Officer to price subsets of E at ADDITIVE
 height by certificate of that subset. Propagate names before any collapse.

# Post-block altitude-ruler. Weighted hit on high true degree for every order.

Strengthens the construction's Economics before assembling the local support
estimate. This proof is for *all* carriers (including E and arbitrary incident
fees and tags and old forced), qualified by the actual `Cash`; no forced
partner dropped. Uses pre-L at `Captain`, no period decision needed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext Repeat Height Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P} {μ a:ℝ}
local notation "Z" => betaF
lemma bigMark (π : ℕ) (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (hm : 0<μ) :
    ∀ᶠ x in atTop, grow G L x ^ π ≤ Real.exp (Q.mark L μ x) ∧
                 grow G L x ^ π ≤ Real.exp (Q.ε*Pressure.Stores.till x) := by
  let d x:= grow G L x; let g x:= Q.mark L μ x
  let a := -1-(π:ℝ); have he': (3/8:ℝ)*(π:ℝ) + a < 0 := by unfold a; have h := Nat.cast_nonneg (α:=ℝ) π; linarith
  have hf : Rate G L a (fun x=> Real.exp (-g x)) := by
    apply (Rate.monitor_cutoff (show 0<μ/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr
    apply Eventually.of_forall; intro x
    dsimp only; rw [Real.rpow_two]; unfold g; change Real.exp (- Delay.hatWin G L _ _ x)=_; unfold Delay.hatWin; congr 1; ring
  have h := Rate.power (G:=G) (L:=L) (a:=3/8)|>.pow π
  filter_upwards [(h.mul hf).below he' 1 zero_lt_one, (h.mul (Rate.cutoff Q.usable (a:=a))).below he' 1 zero_lt_one] with x hx he
  constructor
  · suffices hs : d x ^ π/Real.exp (g x) ≤ 1 from (div_le_one (Real.exp_pos _)).1 hs
    rw [div_eq_mul_inv, ← Real.exp_neg]; exact (le_abs_self _).trans hx
  apply le_of_mul_le_mul_right _ (Real.exp_pos (-Q.ε*Pressure.Stores.till x))
  rw [← Real.exp_add, neg_mul,add_neg_cancel,Real.exp_zero]; exact (le_abs_self _).trans (by simpa only [neg_mul,grow] using he)

-- rooted conventions expose real Cash Φ & w∞. `X` for allowable Expenses.
structure Flint (τπ:ℕ→ℕ) {c f:Side} {S:StepData c f} {T:Tube G S} {W s σ B v : ℝ} {L:Side}
    {R:RG.Rep G f} {o:Target.Order G W} (X : Q.Expense) (π:ℕ) (P': Cash W s μ L Q o σ T R) (j n:ℕ) (κ : Chi)
    {C d q r A u t : ℝ} {k : ℕ} (N : Captain P' j C d v r A u t B q k κ) (Y θ : ℝ) : Prop where
  lion : Leon τπ π N.conduit
  fleet : Armada Q L μ X.earn s θ B j k
  salary_h : collars G θ s j n*(March.salary Q L μ B s j k*(1-1/2)⁻¹)≤ Z G s L ^ X.wanting
  height : Ac.Hit (Captain.reachability (H:=P')) (radiusB s) (fun z=>if Height.tiredT P' τπ π z then N.markΦ z n else 0) X.earn Y

lemma stipulatedS (Q : YM.ConnectedActivityE6.Target G P) (L : Side) (hm : 0 < μ) {B : ℝ→ℝ} (hB : Rate G L 0 B) (k j : ℕ) : Rate G L Q.rate (fun x=> March.salary Q L μ (B x) x j k):= by
  unfold salary; exact (((Rate.const 1).add (hB.mul_left _)).mul (Q.rate_none L hm 0 k 0)).weaken (by linarith)

lemma burns (Q : YM.ConnectedActivityE6.Target G P) (π : ℕ) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W),
    0<W → 0<μ → Q.rate < -(3/8:ℝ) → ∀ e:ℝ, -(3/8:ℝ)*(π:ℝ)+ (3/8:ℝ)+Q.rate < e → ∀ j n χ, ∀ᶠ x:ℝ in atTop,
    ∀ (c' f : Side) (S:StepData c' f) (T:Tube G S), Works P L x S T → Stamp T → ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R), ∀ τπ:ℕ→ℕ, Raw.Productive τπ P T x R →
      ∃ (C' d v t A b r B q i : ℝ) (k : ℕ) (N:Captain H j C' d v t A b r B q k χ), Flint τπ X π H j n χ N (Z G x L ^ e) i := by
  obtain ⟨m,hm⟩:= mountT π P Q; refine ⟨m,fun L hL X W μ c o hW hμ hR e he j n χ=> ?_⟩
  by_cases Hs : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x c f S T h=> (Hs ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hd,hF,hX⟩:=Hs
  obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j χ W hW μ hμ o
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  -- skip
  let f' x:= grow G L x; have hf := Rate.power (G:=G) (L:=L) (a:=3/8)
  have hx': Rate G L (-(3/8:ℝ)*(π:ℝ)) (fun x=> (f' x ^π)⁻¹):= by
    refine Rate.congr Rate.power ?_
    filter_upwards [Delay.shift_pos G L] with x hx
    rw [neg_mul,Real.rpow_neg hx.le,Real.rpow_mul hx.le,Real.rpow_natCast]; rfl
  have hev:= hx'.mul hf|>.mul (hg n 0)
  have hp:= Q.rate_root L hμ (β:=1) (C:=0) -- notation
  filter_upwards [H,hg n 0 X.wanting X.reach,hK,bigMark π Q L hμ, (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1, pressureYoung G L (i:=Q.δ) hp (by linarith),pressureYoung G L (i:=y) (stipulatedS Q L hμ hB k j) (by linarith), hev e he] with x h hh hA he' hx hv hs hr c f S T hW hxP R I τπ hτπ
  obtain ⟨N,hN⟩:= h c f S T (hW.patch hF hX) hxP R _ I τπ hτπ
  simp only [pow_zero,mul_one] at hh hr
  refine ⟨_,_,_,_,_,_,_,_,_,y,k,N,hN,hA,(le_abs_self _).trans hh,fun V=> budget_loosen (pricedT N (Real.one_le_rpow hx (by norm_num)) hN n hA he'.1 he'.2 hv hs V) ?_⟩
  apply le_trans _ ((le_abs_self _).trans hr); apply le_of_eq; unfold f' grow; ring
end YM.AllOrder.High
