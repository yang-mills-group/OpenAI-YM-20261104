import YM.Juniper.Gauze.Carrier
/-!
 # Actual pose storm perturb; output ALL scale budgets conditional lifted stencil (wider than wall). Cost explicit.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Gauze
open Filter Function Metric Lattice Wilson RG Push Push.AbsoluteSums
open Pressure Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel SliceRows Coat
open PhysicalNext PhysicalNext.Repeat Boulevard Blaze Brush Sienna
open Uniform MeasureTheory Push.PriceCompiler Blaze.Frond
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c L: Side} {P : BudgetPoint} {J k u:ℕ}
local notation "X"=>Positions (Uniform.Primary c G)
variable {v a b d w e : ℝ}
section comp
variable {E F Y : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
  [NormedAddCommGroup Y][NormedSpace ℝ Y] {f : E→F} {g:F→Y} {x:E}
lemma shaded (hp:Brush k v d f x)(hs:0<a)(hd:d*a ≤ 1)(hq:v*(d*a) ≤ e)(h : ‖f x‖ ≤ e): Brush k e a⁻¹ f x:= by
   refine ⟨hp.smooth,inv_nonneg.mpr hs.le,?_⟩; rintro (_|i) hi
   · rw [normJ, norm_iteratedFDeriv_zero,pow_zero,mul_one]; exact h
   apply (hp.order _ hi).trans; rw [inv_pow,← div_eq_mul_inv]; refine (le_div_iff₀ (pow_pos hs _)).mpr ?_;rw [mul_assoc,← mul_pow]; apply le_trans _ hq; apply mul_le_mul_of_nonneg_left _ hp.nonneg; exact (pow_le_pow_of_le_one (mul_nonneg hp.pos hs.le) hd (by omega : 1 ≤ i+1)).trans_eq (pow_one _)
lemma storm (hp:Brush k d e f x) (hv:Brush k v d⁻¹ g (f x))(hd: 0<d) : Brush k ( (2:ℝ)^k*(k.factorial*v)) e (fun i=> g (f i)) x:= by
   -- palette charge distinct w scales in/out; cf Brush.trail specialized unit.
   let H:= d • ContinuousLinearMap.id ℝ F; let t:= d⁻¹ • f; have ht i: H (t i)= f i:= by simp [H,t,smul_smul,hd.ne']
   have he: ‖H‖≤d:= by unfold H; rw [norm_smul,Real.norm_of_nonneg hd.le]; exact mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le
   have h':Brush k v 1 (g ∘ H) (t x):= (Brush.reading H ((ht x).symm ▸ hv) he).climb le_rfl (inv_mul_cancel₀ hd.ne').le
   have hS:= hp.smul d⁻¹; rw [norm_inv,Real.norm_of_nonneg hd.le, inv_mul_cancel₀ hd.ne'] at hS; let w:= g ∘ H ∘ t; have hΩ: Brush k (k.factorial*v) ((1+1)*e) w x:= Brush.pine (f:=t) hS h'
   rw [show (fun i=>g (f i))=w from funext (fun i=> congr_arg g (ht i).symm)]
   refine ⟨hΩ.smooth,hp.pos,fun i hi=> (hΩ.order i hi).trans ?_⟩; rw [one_add_one_eq_two,mul_pow,← mul_assoc]; have ht:=hv.nonneg; have hb:=hp.pos
   apply mul_le_mul_of_nonneg_right _ (by positivity); rw [mul_comm ((k.factorial:ℝ)*v)]; gcongr; norm_num -- cost
end comp

-- WORKS paid slim coupling reach at every order after width
section pay
variable (G L)
local notation "z"=> (fun t=> betaF G t L)
local notation "o"=> eaves G L
local notation "r"=> furl G L
local notation "S"=> Uniform.shade G
local notation "R"=> royalty G

def bill : ℝ:= -(15/32:ℝ)
lemma billBelow : bill < 0:= by norm_num [bill]
def slim (x:ℝ):= z x ^ bill
local notation "s"=> slim G L
abbrev reshapeG (T:Snip G) (U : ℝ→ℕ)(x:ℝ)(k:ℕ):Prop :=
   0 < z x ∧ 2*r x < s x ∧ s x ≤ o x ∧ ∀ (c:Side)(w:Positions (Uniform.Primary c G)),c.val≤ U x → ‖w‖ ≤ s x → ∀ a:G.El,
    let t (j:Positions (Uniform.Primary c G)) := putty T (actual j) a; let q (i:Positions (Uniform.Primary c G)):=castle (actual i) a
    Brush k (o x) (s x)⁻¹ t w ∧ q=ᶠ[𝓝 w] actual ∘ t ∧ ‖t w‖ + 2*r x < o x

lemma cashSlim (T:Snip G)(Y : ℝ→ℕ) (hp:Rate G L 0 (fun x=> (Y x : ℝ))) (k:ℕ) : ∀ᶠ t in atTop, reshapeG G L T Y t k := by
    obtain ⟨C,u,hC,hu,H⟩:= chord_chart_cost G; obtain ⟨B,g,hB,hg,hU⟩:= log_chart_cost G; obtain ⟨A,a,hA⟩:= Blaze.Frond.cleanly G k 1 zero_lt_one; obtain ⟨v,hv,hX⟩:= expCost G k 1
    have hs: Rate G L bill (s):= Rate.power; let β x:= S * s x; let f x:= C*β x
    let ξ:= (1+ (k.factorial:ℝ)*v)*(2*S); let d x:= kinStep G (Y x) ξ; let p x:=linearCost (Y x) (f x); have hb: Rate G L bill β:= hs.mul_left _; have hf: Rate G L bill f := hb.mul_left _
    have hk: Rate G L 0 d:= by
       have h : Rate G L 0 (fun x=> mapCost (Y x)*(ξ*R)):= (hp.mul_left _).mul_right _
       exact (((h.mul_right _).add (Rate.const _)).add h)
    have hm: Rate G L bill p:= by
       have ht : Rate G L bill (fun x=> mapCost (Y x)*f x) := by simpa only [zero_add,mapCost] using ((hp.mul_left 4).mul hf)
       exact (ht.add hf).add ht
    have hl: Rate G L bill (fun x=> (1+R)*(d x)*s x):= by simpa only [zero_add] using! ((hk.mul_left (1+R)).mul hs)
    have he: bill < vow:= by norm_num [bill,vow]
    filter_upwards [Delay.shift_pos G L,below' G L hl billBelow zero_lt_one, below' G L hb billBelow (lt_min hu zero_lt_one), below' G L (hm.mul_left G.colorScale) billBelow (lt_min hA.pos T.pos), below' G L hm billBelow hg,
      contraction G L (a:=2) zero_lt_one (Sienna.belt G L) (show -1 < bill by norm_num [bill]), contraction G L (a:=1) zero_lt_one hs he, contraction G L (a:=1) zero_lt_one ((hm.mul_left B).add ((Sienna.belt G L|>.mul_left 2).weaken (show -(1:ℝ)≤bill by norm_num [bill]))) he, contraction G L (a:=k.factorial*A) zero_lt_one hl he] with x hx hw hh ha hh' he hQ hY hv'
    refine ⟨hx, by simpa only [one_mul] using! he, by simpa only [one_mul] using! hQ.le, fun c w hC' hW t=>?_⟩; intro D E
    -- check filter binders let
    have hs₀: 0< s x:= Real.rpow_pos_of_pos hx _; have hs':0<r x:= Real.rpow_pos_of_pos hx _; have hb':0< S:= Uniform.shade_pos G
    have h₂(i): G.chord (castle (actual w) t i) ≤ p x := by
       apply upper hC' t (by unfold f β; positivity); intro i; apply hat_pose w _; intro q hq; have ht: ‖q‖≤ β x:= hq.trans (mul_le_mul_of_nonneg_left hW hb'.le); exact (H q (ht.trans (hh.le.trans (min_le_left ..)))).trans (mul_le_mul_of_nonneg_left ht hC.le)
    have h₃(i): ‖G.mat (castle (actual w) t i) -1‖ < min a T.size:= (chord_dist _).symm.trans_lt ((mul_le_mul_of_nonneg_left (h₂ i) G.colorScale_pos.le).trans_lt ha)
    have hd : Mode actual w k ξ := pose w ((mul_le_mul_of_nonneg_left hW hb'.le).trans (hh.le.trans (min_le_right ..))) hX
    obtain ⟨hΩ,hsΦ⟩:= erect T t actual (lead hC' t hd) hA h₃; have hDpx : ‖D w‖ +2*r x < o x:= by
       apply lt_of_le_of_lt (add_le_add (level T _ t (show 0 ≤ B*(p x) from mul_nonneg hB.le ((G.chord_nonneg _).trans (h₂ (0,0)))) (fun i=> ⟨(h₃ i).le.trans (min_le_right ..),((hU _ ((h₂ i).trans hh'.le)).2).trans (mul_le_mul_of_nonneg_left (h₂ i) hB.le)⟩)) le_rfl); simpa only [one_mul] using! hY
    exact ⟨shaded hΩ hs₀ hw.le (by simpa only [one_mul] using! hv'.le) ((le_add_of_nonneg_right (mul_pos zero_lt_two hs').le).trans hDpx.le),hsΦ,hDpx⟩
end pay
end YM.Juniper.Gauze
