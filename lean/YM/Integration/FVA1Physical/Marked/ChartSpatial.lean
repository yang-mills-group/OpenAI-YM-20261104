import YM.Integration.FVA1Physical.Marked.CurrentRunChart

/-! The Wilson row norm of the exact current conditional field, with all
ordinary coordinate derivative placements summed before testing. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.Uniform RGComparison.Core16.Spool
open RGComparison.Core16.Lam RGComparison.Core16.Catkin MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Rolling MSbar.Whisk
open Next.Foundations Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {c:Side}

abbrev chartKey (u:Operand G c) : Primary c G:=primary u.1 u.2

private theorem chart_span (o:Site c) (l:List (Operand G c)) :
    spanSites (Measuring.chart c G) o (l.map chartKey).get=wordRadius o l := by
  let t:=l.map chartKey
  calc
    _ = ((List.ofFn t.get).map (fun a=>separation o (Measuring.chart c G a))).sum := by
      rw [List.map_ofFn,List.sum_ofFn];rfl
    _ = _ := by rw [List.ofFn_get];simp only [t,List.map_map];rfl

theorem chart_spatial_price (F:Positions (Primary c G) → ℝ) (x:List (Operand G c) → Positions (Primary c G))
    (o:Site c) (q s:ℕ) {α b W:ℝ} (pos:0<α) (b0:0 ≤ b) (W0:0 ≤ W)
    (sm:∀ l,l.length = q → ContDiffAt ℝ q F (x l))
    (words:∀ l,l.length = q → ∀ k:Fin q → Primary c G, ‖YM.Push.Uniform.entry F (x l) k‖ ≤ 
      W*Real.exp (-(((s:ℝ)+1)*α+2*b)*spanSites (Measuring.chart c G) o k)) :
    Yarn q (fun l=>|buoy F (x l) (l.map chartKey)| *spread crest {o} b s l) ≤ 
      (1+2*α⁻¹)^s*(4*Fintype.card G.ColorIndex*countCost α)^q*W := by
  apply rooted_spread_price o q s _ W0 b0 pos (fun _ _=>abs_nonneg _)
  intro l len
  let t:=l.map chartKey
  have lt:t.length = q:=by simp only [t,List.length_map,len]
  have val:buoy F (x l) t=YM.Push.Uniform.entry F (x l) t.get:=RawP.fEntry (sm l len) t lt.le
  have w:‖YM.Push.Uniform.entry F (x l) t.get‖ ≤ W*Real.exp (-(((s:ℝ)+1)*α+2*b)*spanSites (Measuring.chart c G) o t.get) := by
    rw [←lt] at words len
    exact words l len t.get
  rw [chart_span o l] at w
  rw [show buoy F (x l) (l.map chartKey)=YM.Push.Uniform.entry F (x l) t.get from val,←Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left w (Real.exp_pos _).le).trans_eq
  rw [mul_left_comm,←Real.exp_add,show (((s:ℝ)+1)*α+2*b)*wordRadius o l+
    -(((s:ℝ)+1)*α+2*b)*wordRadius o l=0 by ring,Real.exp_zero,mul_one]

variable {I:Type} [Fintype I] {d N n m:ℕ} (R:Run G)
local notation "H" => R.family.path
local notation "RI" => (H).rep N n (m+1)
local notation "RO" => (H).rep N n m
local notation "S" => (H).levels.clock.op m n

theorem current_run_chart_sup (simple:G.Simple) (hm:m < N) (start:R.t 0 ≤ m)
    (a:I → CoverLabel G d) (ready:∀ j,R.t (a j).1.val ≤ m+1)
    (y:Site (R.family.side (m+1) n)) (o:I → Site (R.family.side (m+1) n)) (part:Bool)
    (radius:ℕ) (foot:∀ j,separation (o j-y) 0 ≤ radius) (q s:ℕ) (positive:0<q)
    {α b g:ℝ} (pos:0<α) (b0:0 ≤ b) (base:List (Operand G (R.family.side m n)) → Positions (Primary (R.family.side m n) G))
    (small:∀ l,l.length = q → ‖g•base l‖<1)
    (clear:∀ l,l.length = q → palace (g•base l)∈Boulevard.sunny (RO).p)
    (order:q ≤ (RO).p.order) (room:(((s:ℝ)+1)*α+2*b)*q*(6*(RO).p.B+2:ℝ) ≤ (RO).p.supportExponent) :
    let z:=(S).ratio.parent y
    let v:=fun j=>o j-y
    let φ:=fun U=>look part (tally (freshLamps a) o U)
    let φ₀:=fun U=>look part (tally (freshLamps a) v U)
    let cost:=Doors.rate ((H).S.block m)*birthCost (RI).p (lampSupport a v) ((H).levels.clock.forcedAllowance (m+1))
      (localFieldTariff (RI).p a (R.alloy.B.a.params (m+1)).columns radius+‖(φ₀ 1:ℂ)‖) (2*stencilBound (freshLamps a))
    let F:=fun x=>Bulk.expect S RI (postcard G (R.family.side m n) g x) φ
    Yarn q (fun l=>|buoy F (base l) (l.map chartKey)| *spread crest {z} b s l) ≤ 
      (1+2*α⁻¹)^s*(4*Fintype.card G.ColorIndex*countCost α)^q*(|g|^q*(earnE (RO).p G q*cost)) := by
  intro z v φ φ₀ cost F
  have atWord (l:List (Operand G (R.family.side m n))) (length:l.length = q) := current_run_chart R simple hm start a ready y o part radius foot
    (α:=((s:ℝ)+1)*α+2*b) (by positivity) q (base l) (small l length) (clear l length) order room
  obtain ⟨_,_,_,budget⟩:=current_run_field R simple hm start a ready y o part radius foot
  have co:0 ≤ cost:=by obtain ⟨ea,eb,ha,hb,credit,_⟩:=budget;exact (add_nonneg ha hb).trans credit
  exact chart_spatial_price F base z q s pos b0 (mul_nonneg (pow_nonneg (abs_nonneg g) _) (mul_nonneg (floorP G _ _) co))
    (fun l hl=>(atWord l hl).1) (fun l hl=>(atWord l hl).2 q positive le_rfl)
end YM.Integration.FVA1Physical.Marked
