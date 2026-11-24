import YM.XSpace.Hemline
/-!
# The connected functional along the regulator

Compute the connected 3rd moment at the common lattice placements in the inversion regulator (so same measure), before applying the test with its origin average. Connectedness is that of the PT moment kernels, not requesting to multiply distributions of relative profiles assembled from random center translations. Here the connected array only used for calibration, and not scheduled as nonempty EXACT cumulant. `detail` computes all subset moments in this formula (identical field names & common denominator). All assignments allowed contacts on mesh, limits at indicated separated profiles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter Trace Graph3 Maxwell Maxwell.Free Photo Cirrus Normalize Tornado Chiral Structure1 Lattice AxesTangent PowerSeries
open scoped Topology ContDiff BigOperators Classical
abbrev PS := PowerSeries ℂ
variable {G:Gauge}(W:Initialize G)(V:Normalize.Store G)(g:G.Simple){x: Points 3}
local notation "E"=>missing (tag G)
local notation "U"=>Finset.univ
-- connectedness (all names real labels)
def b3 (P:Badge→PS):PS := P U-(P {0,1}*P {2}+P {0,2}*P {1}+ P {1,2}*P {0})+(2:ℂ) • (P {0}*P {1}*P {2})
def batchT (F:ℕ→Point G 6 3): Badge→PS:=fun k=> PowerSeries.mk (fun i=> F i (E k))
def together (x:Sample 3): PS := b3 (batchT (cooked W V 6 x))
private lemma within (l:Sample 3)(k:Badge) : PowerSeries.map (starRingEnd ℂ) (batchT (cooked W V 6 l) k)=batchT (cooked W V 6 l) k:=PowerSeries.ext fun i=>by rw [coeff_map,batchT,coeff_mk,starRingEnd_apply, ← show cooked W V 6 l i (reel 6 ∘ E k)=_ from cookedR ..,juror] -- star mismatch
lemma real_pt (l:Sample 3)(e:ℕ): star (coeff e (together W V l))= coeff e (together W V l):=by
  let k:=together W V l; change starRingEnd ℂ (coeff e k)=_; rw [← coeff_map]; apply congr_arg; unfold k together b3; simp only [two_smul,map_add,map_mul,map_sub,within]
include W g in
lemma tangent (P:ℕ→ Point G 6 3) (H:P 0=scene x 6)(h:x∈conf 3): coeff 1 (b3 (batchT P))= P 1 (tag G):=by
  have he(s:Badge)(hx:s.Nonempty): constantCoeff (batchT P s)=0:=by rw [← coeff_zero_eq_constantCoeff_apply,batchT,coeff_mk,H]; apply silent W g h s hx -- W not included
  unfold b3; simp only [map_add,map_sub,two_smul,coeff_one_mul,map_mul]; rw [he {1,2}, he {0,2}, he {0,1}, he {1}, he {0}, he {2}]; simp [batchT] -- maybe args
  all_goals decide
include W g in
lemma first_tangent_invariant (P:ℕ→ Point G 6 3)(H:P 0=scene x 6)(s:FieldEnd G 6)(hx:x∈conf 3)(K:s∈ Tri G 6): coeff 1 (b3 (batchT (update P 1 (P 1 + lot (P 0) s))))= coeff 1 (b3 (batchT P)):=by -- name
  rw [tangent W g (update P 1 (P 1 + lot (P 0) s)) (by rw [update_of_ne (show (0:ℕ) ≠1 by decide)]; exact H) hx, tangent W g P H hx]; simp only [_root_.add_apply,H,update_self,stamp_fee (lot _ _),ignored W g x hx s K,mul_zero,add_zero] -- need ensure second stamp update orientation. tune
variable (J:Badge)(hJ:J.Nonempty)
structure Grades (F:Filter (Sample 3))(f:Sample 3→PS): Prop where
 base:Tendsto (fun i=> constantCoeff (f i)) F (𝓝 0)
 first: ∃ x:ℂ,Tendsto (fun i=> coeff 1 (f i)) F (𝓝 x)
namespace Grades
variable {F:Filter (Sample 3)}{f g₁:Sample 3→PS}
lemma prod_n (h:Grades F f)(k:Grades F g₁): Tendsto (fun i=> coeff 1 (f i*g₁ i)) F (𝓝 0):=by obtain ⟨x,hₓ⟩:=h.first; obtain ⟨y,hᵧ⟩:=k.first; simp_rw [coeff_one_mul]; simpa only [mul_zero,add_zero] using (hₓ.mul k.base).add (hᵧ.mul h.base)
lemma prod_b (h:Grades F f)(k:Grades F g₁): Grades F (fun i=> f i*g₁ i):=by refine ⟨?_,0,prod_n h k⟩; simp_rw [map_mul]; simpa using h.base.mul k.base
lemma add (h:Grades F f)(k:Grades F g₁): Grades F (fun i=> f i+g₁ i):=by obtain ⟨x,hₓ⟩:=h.first; obtain ⟨y,hᵧ⟩:=k.first; refine ⟨?_,x+y,?_⟩; simp_rw [map_add]; simpa using h.base.add k.base; simp_rw [map_add]; exact hₓ.add hᵧ
lemma sub (h:Grades F f)(k:Grades F g₁): Grades F (fun i=> f i-g₁ i):=by obtain ⟨x,hₓ⟩:=h.first; obtain ⟨y,hᵧ⟩:=k.first; refine ⟨?_,x-y,?_⟩; simp_rw [map_sub]; simpa using h.base.sub k.base; simp_rw [map_sub]; exact hₓ.sub hᵧ
end Grades
private abbrev K (i:Sample 3) := batchT (cooked W V 6 i) J
include g hJ in
private theorem establishes (h:x∈conf 3): Grades (Gate x) (K W V J):= by
  unfold K batchT; refine ⟨?_, checked1 W V 6 x (E J),?_⟩
  · simp_rw [← coeff_zero_eq_constantCoeff_apply,coeff_mk]; rw [← silent W g h J hJ]; exact scans0 W V 6 _ x h
  simp_rw [coeff_mk]; exact scans1 W V 6 _ x h -- issue
include g in
lemma scanFirst : Senses (conf 3) (fun i=> coeff 1 (together W V i)) (fun x=> checked1 W V 6 x (tag G)):=by
  intro x hx; let f:= K W V; have X(s:Badge)(h:s.Nonempty):= establishes W V g s h hx; have Y := scans1 W V 6 (tag G) x hx; unfold together b3; simp only [map_sub, two_smul,map_add]; have q1:=Grades.prod_n (X {0,1} (by decide)) (X {2} (by decide)); have q2:=Grades.prod_n (X {0,2} (by decide)) (X {1} (by decide)); have q3:=(X {1,2} (by decide)).prod_n (X {0} (by decide)); have qt:= Grades.prod_n (Grades.prod_b (X {0} (by decide)) (X {1} (by decide))) (X {2} (by decide)); have h:Tendsto (fun i=>coeff 1 (batchT (cooked W V 6 i) U)) (Gate x) (𝓝 (checked1 W V 6 x (tag G))):=by simp_rw [batchT, coeff_mk,full]; exact Y
  simpa only [add_zero,sub_zero] using (h.sub ((q1.add q2).add q3)).add (qt.add qt)
end YM.XSpace.Rose
