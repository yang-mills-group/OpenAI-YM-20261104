import YM.RegulatorIR.Profiles.Staple
/-! # Pre-projection of arbitrarily divergent bare columns: kick in NATIVE top units
    Deterministic sup for any relative placements, through any number of slot products,
    before closure & costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Kick
open Budget Budget.Tariff Budget.Premium Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Spatial Set Filter Topology
open Binding Diagram.Formal PertExtension MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient
open Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Halo Halo.Sight Gain Profiles
open Finset Function
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Y I:Type}{p m u a b r s:ℕ}{L: Meter X}
local notation "K"=> Foot G
abbrev posH (k:Foot G):Room:= Geometry.seat 1 k.1
-- need fix notation before
abbrev T (u:ℕ):Tariff (Foot G):= (Tariff.native 1 (by norm_num) u).uses posH
abbrev monetary (u:ℕ)(W:Room):Premium (T (G:=G) u):= (Premium.rooted (Tariff.native 1 (by norm_num) u) W).uses posH


lemma toll_width (q:K)(i:Room): (monetary (G:=G) u i).mark q≠⊤:=by change ENNReal.ofReal _ ^ u≠ ⊤; finiteness
lemma norm_width (q j:K): ((T (G:=G) u)).road q j ≠⊤:= by change ENNReal.ofReal _ ^ u≠ ⊤; finiteness
lemma width_fin (v:Tuple K r)(x:Room): (monetary u (G:=G) x).width v≠⊤:=by
    -- use sup bounds from finite. build manually
    let t:= T (G:=G) u; let B:= monetary (G:=G) u x
    let k:= (1:ℝ≥0∞) + (∑ i:Fin r,∑ j:Fin r,t.road (v i) (v j)) + ∑ j:Fin r,B.mark (v j)
    have h0: k≠⊤:= ENNReal.add_ne_top.mpr ⟨ ENNReal.add_ne_top.mpr ⟨ ENNReal.one_ne_top, ENNReal.sum_ne_top.mpr (fun i _=> ENNReal.sum_ne_top.mpr (fun j _=>norm_width (u:=u) _ _)) ⟩, ENNReal.sum_ne_top.mpr (fun i _=>toll_width (u:=u) _ _) ⟩
    apply ne_top_of_le_ne_top h0; apply B.width_le; swap; exact fun i=> (Finset.single_le_sum (s:=univ) (f:=fun j=> B.mark (v j)) (fun _ _=>zero_le) (Finset.mem_univ i)).trans le_add_self
    exact t.diameter_le (le_self_add.trans le_self_add) fun i j=> (Finset.single_le_sum (s:=univ) (f:=fun j=> t.road (v i) (v j)) (fun _ _=>zero_le) (Finset.mem_univ j)).trans ((Finset.single_le_sum (s:=univ) (f:=fun i=>∑ j,t.road (v i) (v j)) (fun _ _=>zero_le) (Finset.mem_univ i)).trans (le_add_self.trans le_self_add))
lemma boundedly (v:Packet K r)(h:Bounded v)(x:Room)(u:ℕ): markQ (monetary u x) v≠⊤:=by
    unfold markQ quota; rw [tsum_eq_sum (s:=h.toFinset)]
    · exact ENNReal.sum_ne_top.mpr (fun i _=> ENNReal.mul_ne_top (by finiteness) (width_fin (u:=u) _ _))
    intro i hi; rw [show v i=0 from of_not_not (mt h.mem_toFinset.mpr hi)]; simp
lemma untied_bound (A:Packet K p)(B:Packet K r)(u:ℕ)(x:Room): markQ (monetary u x) (untied A B) ≤ markQ (monetary u x) A * markQ (monetary u x) B:=by
 let f:= monetary (G:=G) u x; let g:= (T (G:=G) u); let V:= Tariff.native 1 (by norm_num) u
 have hx (a:Tuple K p)(b:Tuple K r): f.width (Fin.append a b) ≤ f.width a*f.width b:=by
    let w:= Fin.append a b
    have h₁ : f.width a ≤ f.width a * f.width b := le_mul_of_one_le_right zero_le (f.width_unit _)
    have h₂ : f.width b ≤ f.width a * f.width b := le_mul_of_one_le_left zero_le (f.width_unit _)
    refine f.width_le (g.diameter_le ((f.width_unit a).trans h₁) ?_) ?_
    · have hl (i:Fin p)(j:Fin r) : g.road (a i) (b j) ≤ _:= ((V.tri (posH (a i)) x (posH (b j))).trans (mul_le_mul' (show V.road (posH (a i)) x ≤ f.width a from (V.symm ..).trans_le (f.width_ge ..)) (f.width_ge b j)))
      intro i
      refine Fin.addCases (fun i=> ?f) (fun j=>?b0) i
      case f i => refine Fin.addCases ?_ ?_
                  · intro j; rw [Fin.append_left,Fin.append_left]; exact ((g.diameter_ge a _ _).trans (f.width_diameter a)).trans h₁
                  · intro j; rw [Fin.append_left,Fin.append_right]; exact hl i j
      case b0 => refine Fin.addCases ?_ ?_
                 · intro i; rw [Fin.append_left,Fin.append_right,g.symm]; exact hl i j
                 · intro i; rw [Fin.append_right,Fin.append_right]; exact ((g.diameter_ge b _ _).trans (f.width_diameter b)).trans h₂
    refine Fin.addCases (fun i=> by rw [Fin.append_left]; exact (f.width_ge a i).trans h₁) (fun j=>by rw [Fin.append_right]; exact (f.width_ge b j).trans h₂)
 unfold markQ quota; rw [← (Fin.appendEquiv ..).tsum_eq, ENNReal.tsum_prod',← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro i; rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro j
 change ‖untied _ _ (Fin.append i j)‖ₑ * _ ≤ _; rw [untied,Tuple.cutleft,Tuple.cutright,enorm_mul]; exact (mul_le_mul_right (hx i j) _).trans_eq (by ac_rfl)
lemma crisp_budget (u:ℕ)(x:X→Room){A B:X→ Ranked K}(h:∀ i:ℕ,Uniform.Poly L fun k=> markQ (monetary u (x k)) (A k i))(hh:∀ i:ℕ,Uniform.Poly L fun k=> markQ (monetary u (x k)) (B k i)):
   Uniform.Poly L fun k=> markQ (monetary u (x k)) (crisp (A k) (B k) r):=by
    let f k:= monetary u (G:=G) (x k)
    let T(i:ℕ×ℕ)(k:X):= markQ (f k) (pie (A k) (B k) r i)
    have hT(i:ℕ×ℕ)(hv:i∈Finset.antidiagonal r):Uniform.Poly L (T i):=by
       apply ((h i.1).mul (hh i.2)).mono; intro k; unfold T; rw [← Finset.mem_antidiagonal.mp hv,pie,dif_pos rfl]; exact mark_symmetry.trans (untied_bound ..)
    exact (Uniform.Poly.sum _ T hT).mono fun k=> quota_sum ..
def Cheap (L:Meter X)(u p:ℕ)(x:X→Room)(V:X→ Orders (Foot G)) : Prop:= ∀ e≤p,∀ r, Uniform.Poly L fun k=> markQ (monetary (G:=G) u (x k)) (V k e r)
lemma Cheap.choice {x:X→Room}{V W:X→ Orders (Foot G)}(h:Cheap L u p x V)(hh:Cheap L u p x W): Cheap L u p x fun i=>accord (V i) (W i):=by
 intro i hi r; let f(a:ℕ×ℕ)(j:X):= markQ (monetary u (x j)) (crisp (V j a.1) (W j a.2) r)
 refine (Uniform.Poly.sum (Finset.antidiagonal i) f (fun a ha=>?_)).mono fun k=> quota_sum ..
 exact crisp_budget u x (h a.1 (by have he:=Finset.mem_antidiagonal.mp ha; omega)) (hh a.2 (by have he:=Finset.mem_antidiagonal.mp ha; omega))
lemma sight (u:ℕ)(x:Room)(t:Cover)(v:Tuple K r):
   (monetary u x).width (fun i=> carryX t (v i)) ≤ amount 1 u (dist x (Motion.slide 1 t)) * (monetary (G:=G) u 0).width v:=by
 let V:= Tariff.native 1 (by norm_num) u
 let z(i:Fin r):=carryX t (v i); let X:= Motion.slide 1 t;let Y:= amount 1 u (dist x X)
 have h(i:Fin r): posH (z i)= X+posH (v i):= Geometry.dis_seat ..
 have hY: (monetary (G:=G) u 0).width v ≤ Y * (monetary (G:=G) u 0).width v:= le_mul_of_one_le_left zero_le (amount_unit zero_lt_one u dist_nonneg)
 apply (monetary (G:=G) u x).width_le ((T (G:=G) u) |>.diameter_le (((monetary (G:=G) u 0).width_unit v).trans hY) ?_) ?_
 · intro i j; change amount 1 u (dist (posH (z i)) (posH (z j))) ≤ _; rw [h,h,dist_add_left]; exact (( Tariff.diameter_ge (T (G:=G) u) v i j).trans (Premium.width_diameter (monetary (G:=G) u 0) v)).trans hY
 intro i; have ht:= V.tri x X (posH (z i)); change _ ≤ _ * _ at ht -- explicit
 refine ht.trans (mul_le_mul_right ?_ Y); change amount 1 u (dist X (posH (z i))) ≤ _; rw [h i,dist_comm,dist_self_add_left]; convert (monetary (G:=G) u 0).width_ge v i using 1; simp [monetary,Tariff.native,Premium.rooted,Premium.uses]
lemma shifted (V:Packet K r)(h:Bounded V)(u:ℕ)(x:Room)(t:Cover): markQ (monetary (G:=G) u x) (echo (carryX t) V) ≤ amount 1 u (dist x (Motion.slide 1 t))* markQ (monetary (G:=G) u 0) V:=by
 unfold markQ quota; rw [← ENNReal.tsum_mul_left, ← Equiv.tsum_eq (Tuple.winding (carryX t) r)]; apply ENNReal.tsum_le_tsum; intro i; rw [show echo _ V ((Tuple.winding (carryX t) r) i)=_ from echos (carryX t) V i]; exact (mul_le_mul_right (sight u x t i) ‖V i‖ₑ).trans_eq (by ac_rfl)
-- section
lemma prepaid {x:X→Room}{z:X→Cover}(ht:Uniform.Poly L (fun i=> ENNReal.ofReal (dist (x i) (Motion.slide 1 (z i))))) {T:Orders K}(U:ℕ)(hs:∀ e≤p,∀ j, Bounded (T e j)): Cheap L U p x (fun w e r=> echo (carryX (z w)) (T e r)):=by
    intro e he r
    have hc: Uniform.Poly L fun i=> amount 1 U (dist (x i) (Motion.slide 1 (z i))) := by unfold amount; simp_rw [div_one, ENNReal.ofReal_add zero_le_one (show 0≤ dist _ _ from dist_nonneg), ENNReal.ofReal_one]; exact ((Uniform.Poly.standard L ENNReal.one_ne_top).add ht).powQ U
    exact (hc.mul (Uniform.Poly.standard L (boundedly _ (hs e he r) 0 U))).mono fun i=> shifted _ (hs e he r) _ _ _
end YM.RegulatorIR.FVAAlt2.Kick
