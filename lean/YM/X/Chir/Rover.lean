import YM.X.Chir.Touch
/-!
# Limit of continued contacts on separated posts. includes vanishing p--.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Pert (Band.casual Full.toroid)
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
variable {x y: E4}{X Y:Fielding.Walk}
variable (hq:1<q.val)(h:x≠y)(hx:plot q X x)(hy:plot q Y y)
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
def cable (q:ℕ+)(X Y:Fielding.Walk)(d:ℕ)(F:Scaff)(i:ℕ):ℝ:= sprite (epsilon q i) d F (side q i) (transit q X i) (transit q Y i)
lemma lightC {X Y:Fielding.Walk}(u:Cover)(l:List Axis)(j:ℕ): cable q X Y l.length (graphS l u) j= graphK l u (side q j) (X j) (Y j) / (epsilon q j)^(2+l.length):= by unfold cable; rw [← cast_graph,sprite_val,inv_mul_eq_div]; rfl
include h hx hy hq
lemma cope (u:Cover)(l:List Axis): Tendsto (cable q X Y l.length (graphS l u)) L (𝓝 (Band.casual l (x-y)).re):= by
   let z:=x-y; let w:= X-Y+(fun _:ℕ=>u); have hp:plot q w z:= by rw [← add_zero z]; exact (plot.sub hx hy).add (plot.constant hq u)
   have ht : Tendsto (fun i=> graphK l u (side q i) (X i) (Y i)/(epsilon q i)^(2+l.length)) L (𝓝 (Band.casual l (x-y)).re):= by
       apply rpath_casual (paths hq) l (x-y) (sub_ne_zero.mpr h) (fun i=> wrap (side q i) (w i)); exact hp.congr' ((plot_lift hq hp).mono (fun i he=> by exact congr_arg (spot (epsilon q i)) he.symm))
   exact ht.congr fun i=>(lightC u l i).symm
lemma floated (F:Scaff)(hF:F∈air k) : Released (cable q X Y k F):= by
    obtain ⟨a,ha⟩:= glides hq (sky.mp hF) h hx hy; exact ⟨a,ha.congr fun i=>by unfold cable; rw [sprite_val, inv_mul_eq_div]; rfl⟩
lemma sea : Tendsto (fun i=> (ε i)⁻¹^2* green (transit q X i-transit q Y i)) atTop (𝓝 (Green (x-y))):= by
    have he := cope hq h hx hy 0 []; refine he.congr (fun i=>?_); unfold cable; rw [sprite_val, show Interval.green _= h0 _ (transit q X i) (transit q Y i) from (h0_pay ..).symm,inv_pow]; rfl -- inv_pow orientation
omit h hx hy hq
-- universal helic ∆ spin (all), sum formula
lemma leash (n:Side)(e:ℝ)(x y:Site n)(p c:Tet)(r t:ℝ): Wpp e r p t c n x y= -∑ i:Axis,∑ j:Axis, α_pair r p t c i j * sprite e 2 (graphS [i,j] (-step i)) n x y := by
     unfold Wpp; rw [leased]; simp_rw [sprite_val]; simp only [Pi.neg_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; simp only [mul_neg,Finset.mul_sum,mul_left_comm] -- inspect
lemma α_half (p c:Tet) : ∑ i:Axis, α_pair 1 p (-1) c i i=0:= by
     fin_cases p <;> fin_cases c <;> simp only [α_pair,sum4, form] <;> norm_num [form] -- tactic heartbeat
-- u sign cubic polynomial evaluated on arbitrary vector x, normal.Sea
def matrixU (x: E4) (p c:Tet):ℝ:= - ∑ i:Axis,∑ j:Axis, α_pair 1 p (-1) c i j * (x i*x j)
def opportunity (x:E4) (p c:Tet)(r t:ℝ):= - ∑ i:Axis,∑ j:Axis, α_pair r p t c i j * Maxwell.grad i (Maxwell.grad j Green) x
def solar (x:E4)(p c:Tet):ℝ:= 8*normal*matrixU x p c * (‖x‖^2)⁻¹^3
lemma leverage {x:E4}(h:x≠0) (p c:Tet): opportunity x p c 1 (-1) = solar x p c:= by
    unfold opportunity solar matrixU; let W:=(‖x‖^2)⁻¹^2; let b:= ‖x‖^2; have he (i:Axis) : (∑ j:Axis, α_pair 1 p (-1) c i j*(-2*normal*(YM.basis i j)*W)) = α_pair 1 p (-1) c i i*(-2*normal)*W:= by
         rw [sum_eq_single i]; simp [mul_assoc,basis_eq]; intro b _ hb; simp [basis_eq,hb,Ne.symm hb];simp
    dsimp only [W] at he; simp_rw [Maxwell.second_Green h, mul_add,Finset.sum_add_distrib, he]; rw [← Finset.sum_mul,← Finset.sum_mul, α_half]; simp only [zero_mul,zero_add]; simp only [mul_neg,neg_mul, Finset.sum_mul, Finset.mul_sum]; congr 1; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
include h hx hy hq
lemma starW (p c:Tet)(r t:ℝ): Tendsto (fun i=> Wpp (ε i) r p t c (side q i) (transit q X i) (transit q Y i)) L (𝓝 (opportunity (x-y) p c r t)):= by
    simp_rw [leash]; apply Tendsto.neg; refine tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ fun j _=>?_); exact (cope hq h hx hy (-step i) [i,j]).const_mul _
lemma turbine (p c:Tet) : Tendsto (fun i=> Wpp (ε i) 1 p (-1) c (side q i) (transit q X i) (transit q Y i)) atTop (𝓝 (solar (x-y) p c)):= leverage (sub_ne_zero.mpr h) p c ▸ starW hq h hx hy _ _ 1 (-1)
-- Opp vanishing by contraction anti+trace.Harm.
omit h hx hy hq
lemma chance (p c:Tet){x:E4}(h:x≠0): opportunity x p c (-1) (-1)=0:= by
   let F(y z:Axis):= η_at p c z y* Maxwell.grad y (Maxwell.grad z Green) x; have he : ∑ i: Axis,∑ j:Axis,F i j=0:= by
       have ht : ∑ i: Axis,∑ j:Axis,F i j=-∑ i:Axis,∑ j:Axis,F i j:= by nth_rw 1 [sum_comm]; simp only [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; unfold F; rw [η_at_flips p c i j,neg_mul,Maxwell.Hess_sym h i j]; -- orientation
       linarith
   unfold opportunity; simp_rw [α_mm,sub_mul,Finset.sum_sub_distrib]; unfold F at he; rw [he]; by_cases hz:p=c <;> simp [hz,ite_mul, Maxwell.harmonic h]
include hq h hx hy
lemma turbine_same (p c:Tet): Tendsto (fun i=>Wpp (ε i) (-1) p (-1) c (side q i) (transit q X i) (transit q Y i)) atTop (𝓝 0) := chance p c (sub_ne_zero.mpr h) ▸ starW hq h hx hy p c (-1) (-1)
end YM.PositionX.Chir
