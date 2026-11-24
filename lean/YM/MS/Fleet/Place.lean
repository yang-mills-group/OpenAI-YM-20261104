import YM.MS.Fleet.Envelope
/-!
Geometry to take large orbit without changing offsets at any fixed i. Keep both M.bar and
 cover anchors independent of addresses. Quantitative revelation of cash_out.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Flux Wire Book Convolve Orbit Cog Orbit.LogReal
open Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Puff.Mom Vista
open scoped Topology ContDiff Interval
variable {I W:Type}{G:Gauge}{L:I→ Side}{S:I→Cover}
-- cutoff sequence for fixed-offset auxiliary. side=4n in native.$z.Other later
def walkway (n:ℕ): Side:=⟨ 2*(n+1),by omega ⟩
def crane (n:ℕ): Cover:= fun i=> if i=0 then (n+1:ℕ) else 0
local notation "Ϝ"=> dimT walkway
lemma fullC (n:ℕ): ((Ϝ) n).val=4*(n+1):= by rw [dimT,cap_val]; change 2*(2*(n+1))=4*(n+1); ring
lemma centerD (n:ℕ): crane n= Lattice.lift ( wrap (dimT walkway n) ( crane n )):= by
   symm; apply lift_eq_iff.mpr ⟨ rfl,fun i=>?_⟩; unfold crane; rw [fullC]; split <;> omega
lemma distC (n:ℕ): pdist ( wrap (Ϝ n) ( crane n ))= n+1 := by
    unfold pdist; simp_rw [ ← centerD ]; unfold crane; apply le_antisymm; · refine Finset.sup_le ?_; intro i _; split <;> omega
    refine le_trans (le_of_eq ?_) (Finset.le_sup (b:=0) (f:=fun i:Axis=> Int.natAbs ( if i=0 then ((n+1:ℕ):ℤ) else 0)) (Finset.mem_univ _)); simp; omega
lemma Cleared : Clearance walkway crane:= by
    intro i x; unfold Vista.mine; nth_rw 1 [fullC]; by_cases hx:x=0; · rw [ hx,map_zero,sub_zero,distC ]; omega
    let t:= thin ( walkway i ) x; let y:= wrap ((Ϝ) i) (crane i); have he:pdist t ≤ pdist y + pdist (y-t) := by nth_rw 1 [ show t=y+ -( y-t ) from (by abel)]; exact ( pdist_triangle _ _ ) |>.trans_eq (by rw [pdist_neg]);
    have hz : pdist t=(2*(i+1)):= by rw [show pdist t=( walkway i ).val* pdist x from Vista.caress ..,bornlf _ hx, Nat.mul_one]; rfl -- via Ratio
    have hv:=distC i; unfold y t at he hz; omega
lemma scaleWalk : Vista.width walkway crane:= centered_size _ _ centerD
lemma pay_repr {V:Visa I}{f:I→ℂ}(h: cash_out V L f): ∃ (C:ℝ), 0<C ∧ ∃ k:ℕ,∀ i, ‖f i‖ ≤ C*( V.bank i*(1+ log (1+ tickA L i)))^k*(tickA L i)^(-eps_gain):= by
    obtain ⟨C,hC,k,h⟩:=h; exact ⟨ C,hC,k,fun i=> by specialize h i; rw [toboot,wallet, abs_of_nonneg (φ_day L i)] at h; exact h ⟩
-- natural log* disappearing with Dwind
lemma exp_keep (x:ℝ)(h:0<x)(n:ℕ)(C:ℝ): Tendsto (fun v:ℝ=>(C+v)^n* exp (-x*v)) atTop (𝓝 0):= by
    have he:Tendsto (fun y:ℝ=> y^n* exp (-x*y)) atTop (𝓝 0):= by simpa only [Real.rpow_natCast] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n x h
    obtain hh : Tendsto (fun y:ℝ=> C+y) atTop atTop:= tendsto_atTop_add_const_left atTop C tendsto_id; convert! ( ( he.comp hh).mul_const (exp ( x*C )) ) using 1; · ext v; simp only [Function.comp_apply,mul_assoc,← exp_add]; ring_nf
    rw [zero_mul]
-- replace log (1+s)≤ log (2⋅s). In Scope.
lemma timeW {f:Filter I}{V:I→ℝ}(h:Tendsto V f atTop)(hc:∀ i,1≤V i)(x:ℝ)(hx:0<x)(k:ℕ) : Tendsto (fun i=> (1+log (1+V i))^k*(V i)^(-x)) f (𝓝 0) := by
    obtain H : Tendsto (fun i=> (1+log 2+log (V i))^k* exp (-x*log ( V i ))) f (𝓝 0) := (exp_keep x hx k _ ).comp (tendsto_log_atTop.comp h); have hv(i):0< V i:= lt_of_lt_of_le zero_lt_one ( hc i ); have hP(i): 0≤1+log (1+V i):= by have he:=log_nonneg (show 1≤1+V i from (by linarith [hv i])); linarith
    apply squeeze_zero (fun i=> by have h:=hP i; have ht:=hv i; positivity) _ H; intro i; rw [Real.rpow_def_of_pos ( hv i ),mul_comm (log _)]; apply mul_le_mul_of_nonneg_right _ ( exp_pos _ |>.le ); apply pow_le_pow_left₀ ( hP i )
    rw [add_assoc _ (log 2)]; apply add_le_add_right ?_ 1; rw [← Real.log_mul (by norm_num) ( hv i |>.ne' )]; apply log_le_log ( by have ht:=hv i; linarith ); linarith [hc i]
lemma Timed {V:Visa ℕ}{f:ℕ→ℂ}(hp:cash_out V walkway f){t:ℝ}(ht:∀ i,V.bank i=t): Tendsto f atTop (𝓝 0):= by
   let p:=tickA walkway; obtain h : Tendsto p atTop atTop:= by unfold p tickA; simp_rw [fullC]; exact tendsto_natCast_atTop_atTop.comp ( ( show StrictMono (fun x:ℕ=>4*(x+1)) from fun x y hx=> by dsimp only; omega ).tendsto_atTop )
   obtain ⟨C,hC,k,H⟩:= pay_repr hp; let v(i:ℕ):= (1+ Real.log (1+p i))^k*p i^(-eps_gain); have he:Tendsto v atTop (𝓝 0):= timeW h ( δ_L walkway ) _ p_gain k; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun _=> norm_nonneg _) (fun i=>?_ ) ( (by simpa using he.const_mul (C*t^k) ) : Tendsto (fun i=>C*t^k*v i) atTop (𝓝 0))
   obtain hp:= H i; rw [ ht, mul_pow ] at hp; apply hp.trans; dsimp only [v,p]; ring_nf; rfl
end YM.MS.Fleet
