import YM.MSbar.RawP.Grit
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open AnalyticBridge.SectorAffine.Offset
variable {G:Gauge}{n:Side}{σ E ι:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype σ]
open AnalyticBridge.SectorAffine Metric Pressure
variable {G:Gauge}{n:Side}
variable {p:ℕ}{a b C K r:ℝ}
local notation "W"=> Positions (Primary n G)
local notation "ℓ"=>Measuring.chart n G
noncomputable def sparkP (s:Signed)(x:Positions (Primary n G)):= pull s 0 (palace x)
variable (s:Signed)(b' :Site n)(q:Bond n)
lemma prospect (z:ℕ)(hp:separation b' q.1+1 ≤ z) : Requests Set.univ (fun x:W=>sparkP s x q) (Measuring.chart n G) (affine s 0 b') z:=by
    intro x _ y _ hg; let t:=(posDir q.2).rotate s; let u:= affine s 0 q.1; have hv:separation (affine s 0 b') (t.used u).1 ≤ z:=by apply (separation_triangle _ u _).trans; refine (Nat.add_le_add (le_of_eq (AnalyticBridge.VerifiedReset.spin_separation s _ b' q.1)) (letter_position u t)).trans hp
    change t.read _ u=t.read _ u; have hh:palace x (t.used u)=palace y (t.used u):=by
        exact Eq.trans (Work.F03.represent_link ((tint G _) x) _) ((congr_arg G.lieExp (show tint G _ x ((t.used u).1, Exterior.coord (t.used u).2)=tint G _ y _ from by ext k; exact hg _ hv)).trans (Work.F03.represent_link ((tint G _) y) _).symm)
    unfold Step.read; rw [hh]
lemma whirls (w : Walk)(x:Site n)(h:w.length+1≤ p) : Requests Set.univ (fun v:W=> travel (sparkP s v) x w) (Measuring.chart n G) (affine s 0 x) p:=by
    intro i hi j hj he; refine path_same fun q hq=> prospect s x q _ (by omega) i hi j hj he
variable (x : Positions (Primary n G)) (h:PaintSupply G p K) (hx:‖x‖≤1)
local notation "Q"=> outerCost G p K
include h hx
lemma votes : Allows p (fun x:Positions (Primary n G)=> G.mat (sparkP s x q)) x Q:=by
    let U:= @palace G n; have ht(i:Pressure.Bond n) : Allows p (fun x:W=> G.mat (U x i)) x Q:=by
        let L:W→L[ℝ]G.Color:= (ContinuousLinearMap.proj (φ:=fun _ : Body 1 n=> G.Color) (R:=ℝ) (i.1,Exterior.coord i.2)).comp (tint G _).toContinuousLinearMap
        have hL: ‖L‖ ≤ shade G:=by apply L.opNorm_le_bound (shade_pos G|>.le); exact fun t=> (norm_le_pi_norm ((tint G _) t) _).trans (tint_le t)
        have hv:‖L x‖ ≤ shade G:= (L.le_opNorm _).trans ((mul_le_mul hL hx (norm_nonneg _) (shade_pos ..|>.le)).trans_eq (mul_one _)); have hh(t:W):U t i=G.lieExp (L t):=Work.F03.represent_link ((tint G _) t) i; simp_rw [hh]; exact (h.2 _ hv).comp (f:=L) (allows_linear hL hv)
    unfold sparkP pull Step.read; split; exact (ht _).inverse (f:=fun x=> U x _); exact ht _
lemma supplyS (v:Slot)(b:Site n): Allows p (fun x: W => v.atSite (sparkP s x) b) x (curvatureCost G * travelCost G p (2*v.length) Q):=by
    simp_rw [Work.F02.atSite_curvature]; refine curvature_price (U:=fun x:W=> travel (sparkP s x) b (Work.F02.slotWalk v)) (travel_jets (U:=fun x:W=> sparkP s x) (fun j=> votes s j x h hx) b ?_); simp only [Work.F02.slotWalk,List.length_append,Lattice.reverse,List.length_map,List.length_reverse]; change v.walk.length+4+_ ≤ 2*(v.walk.length+4); omega
omit h hx
lemma supplyR(v:Slot)(b:Site n): Requests Set.univ (fun x: W => v.atSite (sparkP s x) b) (Measuring.chart n G) (affine s 0 b) (2*v.length+1):=by
    intro i hi j hj he; change _= v.atSite _ _; simp_rw [Work.F02.atSite_curvature]; apply congr_arg; refine whirls s (Work.F02.slotWalk v) b ?_ _ hi _ hj he; simp only [Work.F02.slotWalk,List.length_append,Lattice.reverse,List.length_map,List.length_reverse]; change v.walk.length+4+_+1 ≤ 2*(v.walk.length+4)+1; omega
-- gains q width choose suff, avoid κ.u.
lemma fund (G:Gauge)(p:ℕ)(a:ℝ)(ha:0<a)(K:ℝ)(h:PaintSupply G p K) : ∃ B:ℝ,1 ≤B ∧∀ n:Side, ∀ i:Slot,∀ s:Signed,∀ b:Site n,∀ x:Positions (Primary n G), ‖x‖≤1 → Allows p (fun x=> i.atSite (sparkP s x) b) x (B*Real.exp (a*i.length)):=by
    obtain ⟨V,hV,hh⟩:= AnalyticBridge.SectorAffine.travel_coupon G p (outerCost G p K) (outer_pos G p h.1 |>.le) (half_pos ha)
    refine ⟨max 1 (curvatureCost G *V),le_max_left ..,fun n i s b x hx=> (supplyS s x h hx i b).mono ?_⟩; have ht:= (mul_le_mul_of_nonneg_left (hh (2*i.length)) (curvature_nn G)); rw [←mul_assoc,show a/2*(↑(2*i.length):ℝ)=a*i.length from (by push_cast; ring)] at ht; exact ht.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _|>.le))
end YM.MSbar.RawP
