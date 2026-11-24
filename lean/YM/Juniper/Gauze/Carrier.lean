import YM.Juniper.Gauze.Ambient
/-!
# Re-aiming for stencil. Costs on y, calibrated but gauge after exp.

Here one width ESSENTIALLY smaller (Slim) for derivatives than that in
`Tender`, for poly-log price gauges. Cannot weaken budget radius without also
repaying permits at TRUE seams. Use successor leaps after purchase below.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Gauze
open Filter Function Metric Lattice Wilson RG Push Push.AbsoluteSums
open Pressure Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel SliceRows
open PhysicalNext PhysicalNext.Repeat Boulevard Blaze Brush Sienna
open Uniform MeasureTheory
open Blaze.Frond
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c L: Side} {P : BudgetPoint} {J k u:ℕ}
local notation "X"=>Positions (Uniform.Primary c G)
variable {v a b w : ℝ}
def mapCost (u:ℕ) := 4*(u:ℝ)
lemma compass (z x:Site c)(h:c.val≤u) : ((carriage z x).length:ℝ) ≤ mapCost u:= by
   apply le_trans (Nat.cast_le.mpr (SliceRows.mileage z x)); unfold mapCost; norm_cast; apply Nat.mul_le_mul_left; apply le_trans _ h; unfold separation pdist; refine Finset.sup_le (fun i hi=>?_); have ht:=Lattice.lift_centers (z-x) i; change (lift (z-x) i).natAbs ≤ c.val; omega
section estimator
variable {E :Type}[NormedAddCommGroup E][NormedSpace ℝ E] {W:E→ Config G c} {x:E}
local notation "R"=> royalty G
def kinStep (G:Gauge) (u:ℕ) (d:ℝ) := (mapCost u*(d*royalty G))*royalty G+(d*royalty G)+(mapCost u*(d*royalty G))
lemma lead (h:c.val≤u) (a:G.El)(hh:Mode W x k b):Mode (fun i=> castle (W i) a) x k (kinStep G u b):= by
   let f x:= gauge (SliceRows.carrier 0 (W x)) (W x); have hr:0≤R:=zero_le_one.trans (royalty_ge _); have hb:= hh.pos; apply Blaze.soak (U:=f)
   let s:=mapCost u*(b*R)
   have hx(i:Site c):Brush k R s (fun j=> G.mat (carrier 0 (W j) i)) x:= (tour (U:=W) _ _ hh.pos hh.atLink).climb le_rfl (mul_le_mul_of_nonneg_right (compass 0 i h) (mul_nonneg hb hr))
   constructor
   · unfold kinStep mapCost; positivity
   intro i; let t j:= carrier 0 (W j) (i.1+step i.2); let Z j:= G.mat ((t j)⁻¹)
   let J:= R; have hz: Brush k R s Z x:= Blaze.reverse (f:=t) (hx _)
   have hy (i:Bond c):= hh.atLink i; have hp: max 1 J ≤J:= max_le (royalty_ge _) le_rfl
   unfold kinStep; rw [add_assoc]; simp_rw [show ∀ x, f x i=carrier 0 (W x) i.1*(W x i*(t x)⁻¹) from fun x=> mul_assoc ..]
   exact Blaze.links (f:=fun x=> carrier 0 (W x) i.1) (hx _) (Blaze.links (hy i) hz _ hp) _ hp

def linearCost (u:ℕ)(b:ℝ):= (mapCost u*b + b)+(mapCost u * b)
lemma upper (h:c.val≤u) (a:G.El) (ht:0≤v)(W:Config G c)(hw:∀ i,G.chord (W i) ≤ v)(i:Bond c): G.chord (castle W a i) ≤ linearCost u v:= by
   change G.chord (a*(Lattice.gauge (SliceRows.carrier 0 W) W i)*a⁻¹)≤_; rw [G.chord_conj]
   have he(i:Site c):G.chord (SliceRows.carrier 0 W i) ≤ mapCost u*v:= (Next.Fluctuations.travel_chord _ _ _ v hw).trans (mul_le_mul_of_nonneg_right (compass 0 i h) ht)
   exact (G.chord_triangle ..).trans (add_le_add ((G.chord_triangle ..).trans (add_le_add (he _) (hw _))) ((G.chord_inv ..).trans_le (he _)))
lemma hat_pose (x:X)(hp:∀ p:G.Color, ‖p‖ ≤ Uniform.shade G*‖x‖ → G.chord (G.lieExp p) ≤ v)(i : Bond c): G.chord (actual x i) ≤ v:= by rw [actual,represent_link]; exact hp _ ((norm_le_pi_norm (Uniform.tint G _ x) _).trans (Uniform.tint_le x))
lemma pose (x:X)(hp:Uniform.shade G*‖x‖≤1)
   (hJ:∀ a:G.Color, ‖a‖≤1 → Brush k v 1 (fun x=> G.mat (G.lieExp x)) a) : Mode actual x k ((1+ k.factorial*v)* (2 * Uniform.shade G)):= by
   let b:=Uniform.shade G; have hb:0<b:= shade_pos _; have hv:=(hJ 0 (by simp)).nonneg
   refine ⟨by positivity,fun i=> ?_⟩
   let L':= tint G (Body 1 c); let t : X→L[ℝ] G.Color:= (ContinuousLinearMap.proj (pole i)).comp L'.toContinuousLinearMap; have he x: ‖t x‖≤b*‖x‖:= (norm_le_pi_norm (L' x) _).trans (Uniform.tint_le x); have hG:‖t x‖≤1:= (he x).trans hp
   have hh : Brush k 1 b t x:= Brush.linearB t hG (by rw [one_mul]; exact ContinuousLinearMap.opNorm_le_bound _ hb.le he) hb.le
   have hh:= Blaze.thicken (f:=fun x=> G.lieExp (t x)) (hh.pine (hJ _ hG))
   rw [show (1+1:ℝ)=2 from by norm_num] at hh; simp_rw [actual,Work.F03.represent_link]; exact hh

variable (T:Snip G)
set_option maxHeartbeats 420000 in
lemma erect (a:G.El)(W:E→ Config G c)(h:Mode (fun t=> castle (W t) a) x k v) (he:Suitable G k w b 1)
    (hp:∀ i,‖G.mat (castle (W x) a i) - 1‖ < min b T.size) : Brush k (k.factorial*w) ((1+royalty G)*v) (fun t=> putty T (W t) a) x ∧ (fun t=> castle (W t) a) =ᶠ[𝓝 x] (actual ∘ fun t=>putty T (W t) a) := by
   let f (t:E) i:= G.plog (G.mat (castle (W t) a i))
   let P(t:E) := toLog (f t); obtain ⟨ht,-,hF⟩:= Blaze.Frond.ep h he (fun i=> (hp i).le.trans (min_le_left ..))
   have hh(i: Bond c) : ∀ᶠ t in 𝓝 x, ‖G.mat (castle (W t) a i)-1‖ ≤ T.size:= ((h.atLink i).smooth.continuousAt.sub (continuousAt_const (y:=(1:G.Mat)))).norm.eventually (ge_mem_nhds ((hp i).trans_le (min_le_right ..)))
   let L':= tint G (Body 1 c); have hf : (fun t=> putty T (W t) a)=ᶠ[𝓝 x] (L'.symm ∘ P):= by
     filter_upwards [eventually_all.mpr hh] with t ht; unfold P; rw [putty_eq,Function.comp_apply]; congr 2; funext j; exact T.stays _ (ht _)
   have he : Brush k (1*(k.factorial*w)) _ (L'.symm ∘ P) x:= ht.report L'.symm.toContinuousLinearMap (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t=> by rw [one_mul]; exact Uniform.tint_inv_le t); rw [one_mul] at he
   refine ⟨he.shimmy hf,?_⟩; filter_upwards [hF,hf] with t h hT; change castle _ _=actual (putty T (W t) a); rw [hT]; unfold L' P actual Function.comp; rw [ContinuousLinearEquiv.apply_symm_apply]; exact h
lemma level (T:Snip G) (W:Config G c) (a:G.El)(hv:0≤v)(he:∀ i,‖G.mat (castle W a i)-1‖ ≤ T.size ∧ ‖G.plog (G.mat (castle W a i))‖ ≤ v): ‖putty T W a‖ ≤ v:= by
   rw [putty_eq]; apply le_trans (tint_inv_le (G:=G) _); apply (pi_norm_le_iff_of_nonneg hv).2; intro i; let j: Bond c:= (Work.E03.poleEquiv _).symm i; change ‖T.out (G.mat (castle W a j))‖ ≤ v; rw [T.stays _ (he j).1]; exact (he j).2
end estimator
end YM.Juniper.Gauze
