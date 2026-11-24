import YM.RegulatorIR.Capture.Stock

/-!
# Exact center cells and h=0 normalized capture

Translation of output keeps axes and measure. Pay arbitrary discontinuity at
boundary only outside mean. Canonical ancestors (no truncating old radii).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Capture
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
variable {l P:ℝ}
def seatX (v:ℝ) : Set Room:= cube (same (-v/2)) v
lemma seatCaps (_hl:0≤l):seatX l⊆ Metric.closedBall 0 l:=by
 intro x hx; rw [Metric.mem_closedBall,dist_zero_right]; refine (pi_norm_le_iff_of_nonempty _).mpr (fun i=> ?_)
 have h:= inside.mp hx i;change -l/2≤x i ∧ x i < -l/2 +l at h;rw [Real.norm_eq_abs,abs_le]; constructor <;> linarith
lemma seatIn {f:Room→ℝ}(h:Continuous f)(hl:0 ≤ l): IntegrableOn f (seatX l):= IntegrableOn.mono_set (h.continuousOn.integrableOn_compact (isCompact_closedBall 0 l)) (seatCaps hl)
def weighT (l:ℝ)(f:Room→ℝ):= weigh (same (-l/2)) l f
lemma seatScale (z:ℝ)(f:Room→ℝ): weighT l (fun x=>z*f x)=z*weighT l f:=by unfold weighT weigh accrue; rw [MeasureTheory.integral_const_mul,mul_div_assoc]
lemma seatSum (t:Finset I)(F:I→Room→ℝ)(h:∀ i∈t,IntegrableOn (F i) (seatX l)) : weighT l (fun x=>∑ i∈t,F i x)=∑ i∈t,weighT l (F i):=by change (∫ x in seatX l,(∑ i∈t,F i x))/l^4= _;rw [MeasureTheory.integral_finsetSum _ h, Finset.sum_div]; rfl
lemma seatCongr (l:ℝ){f g:Room→ℝ}(h:∀ x∈seatX l,f x=g x): weighT l f= weighT l g:=by unfold weighT weigh accrue;rw [setIntegral_congr_fun (seen ..) h]
-- exact tiling at odd ratios, offset all positions.
variable (t:Side)
abbrev location (l:ℝ)(x: Site t):Room:= slide l (Lattice.lift x)
def seatTile (l:ℝ)(x: Site t):Set Room:= cube (location t l x+same (-l/2)) l
lemma shiftedX (i:Site t) (g:Room→ℝ):
 (∫ y in seatTile t l i, g y)=(∫ y in seatX l,g (location t l i+y)):=by
 rw [← MeasureTheory.integral_indicator (show MeasurableSet (seatTile t l i) from seen ..),← MeasureTheory.integral_indicator (show MeasurableSet (seatX l) from seen ..)]
 let s:= location t l i; rw [← integral_add_left_eq_self (μ:=volume) ((seatTile t l i).indicator g) s];apply integral_congr_ae;filter_upwards with x
 by_cases hx:x∈ seatX l
 · rw [indicator_of_mem (show s+x∈seatTile t l i from (Centered.drift (same (-l/2)) s l x).mp hx),indicator_of_mem hx]
 rw [indicator_of_notMem (show s+x∉ seatTile t l i from fun h=> hx ((Centered.drift _ s l x).mpr h)),indicator_of_notMem hx]
lemma respects (hl:0<l) : Pairwise (Function.onFun Disjoint (seatTile t l)):= by
 intro i j he; apply Set.disjoint_left.mpr; intro x h₁ h₂; apply he; apply_fun Lattice.lift -- inj?
 · ext1 v; obtain ⟨p,q⟩:= inside.mp h₁ v; obtain ⟨a,b⟩:= inside.mp h₂ v
   let y:= Lattice.lift i v; let z:=Lattice.lift j v
   change l * (y:ℝ) + -l/2 ≤ x v at p; change x v<l*(y:ℝ)+-l/2+l at q; change l * (z:ℝ) + -l/2 ≤ x v at a;change x v< l*(z:ℝ)+-l/2+l at b
   have hx: (z:ℝ)< (y:ℝ)+1 := lt_of_mul_lt_mul_left (a:=l) (by nlinarith) hl.le
   have hy: (y:ℝ)< (z:ℝ)+1:= lt_of_mul_lt_mul_left (a:=l) (by nlinarith) hl.le
   have hv : (z:ℤ) < y+1:=by exact_mod_cast hx
   have hu : (y:ℤ) < z+1:=by exact_mod_cast hy
   change y=z;omega
 · intro i j h; exact (wrap_lift i).symm.trans ((congr_arg (wrap _) h).trans (wrap_lift ..))

lemma gives (hl:0<l)(ht:Odd t.val): seatX (l*t.val) = ⋃ i,seatTile t l i:=by
 ext x; rw [mem_iUnion]
 constructor
 · intro h
   let p (v:Axis):ℤ:= ⌊x v /l+ (1/2:ℝ)⌋
   have hx i : (p i:ℝ) ≤ x i/l+1/2:=Int.floor_le _
   have he i : x i/l+1/2< (p i:ℝ)+1:= Int.lt_floor_add_one _
   have hp:Lattice.lift (wrap t p)=p:=by
      obtain ⟨s,hs⟩:=ht
      apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; obtain ⟨a,b⟩:= inside.mp h i
      change -(l*t.val)/2 ≤ x i at a; change x i < -(l*t.val)/2+l*t.val at b; rw [hs] at a b; push_cast at a b
      have hh : -(s:ℝ) ≤ x i/l+1/2:=by rw [← sub_le_iff_le_add,le_div_iff₀ hl]; linarith
      have hV : p i < (s:ℤ)+1:=by apply Int.floor_lt.mpr; push_cast; rw [← lt_sub_iff_add_lt,div_lt_iff₀ hl]; linarith
      have hx: -(s:ℤ) ≤ p i:= Int.le_floor.mpr (by exact_mod_cast hh)
      omega
   refine ⟨wrap t p,inside.mpr (fun i=>?_)⟩
   change l*(Lattice.lift _ i:ℝ)+ -l/2≤ _ ∧ _<l*(Lattice.lift _ i:ℝ)+ -l/2+l; rw [hp]
   constructor
   · have hv:= (hx i); rw [← sub_le_iff_le_add, le_div_iff₀ hl] at hv; linarith
   have hz:=he i; rw [← lt_sub_iff_add_lt, div_lt_iff₀ hl] at hz;linarith
 rintro ⟨i,hi⟩; apply inside.mpr; intro v; obtain ⟨a,b⟩:=inside.mp hi v; let z:=Lattice.lift i v
 obtain ⟨s,hs⟩:=ht; have hx:= lift_centers i v
 have hz : -(s:ℝ) ≤ (z:ℝ):= by exact_mod_cast (show -(s:ℤ) ≤ z from by unfold z;omega)
 have ht : (z:ℝ) ≤ (s:ℝ):= by exact_mod_cast (show z ≤ (s:ℤ) from by unfold z;omega)
 change l*(z:ℝ)+ -l/2≤ x v at a; change x v < l*(z:ℝ)+ -l/2+l at b
 change -(l*t.val)/2≤ _ ∧ _< -(l*t.val)/2+l*t.val; rw [hs]; push_cast;constructor<;> nlinarith
lemma meanTiles (hl:0<l)(ht: Odd t.val){f:Room→ℝ}(Z: IntegrableOn f (seatX (l*t.val))) : weighT (l*t.val) f = tally t 0 * ∑ v: Site t,weighT l (fun x=>f (location t l v+x)):=by
 have hx:(∫ x in seatX (l*t.val),f x) = ∑ i:Site t,(∫ x in seatTile t l i,f x):=by
    rw [gives t hl ht, MeasureTheory.integral_iUnion (fun i:Site t=> show MeasurableSet (seatTile t l i) from seen ..) (respects t hl),tsum_fintype]; rw [← gives t hl ht]; exact Z
 change _ / _=_*∑ i:Site t,_ / l^4; rw [show accrue f (same (-(l*t.val)/2)) (l*t.val)=_ from hx];simp_rw [shiftedX]; unfold tally display; rw [← Finset.sum_div,mul_pow];change _/_= _*((∑ i:Site t,∫ x in seatX l,f (location t l i+x))/l^4); ring -- denominators
end YM.RegulatorIR.Capture
