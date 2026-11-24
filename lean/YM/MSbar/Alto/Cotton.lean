import YM.MSbar.Alto.Siege
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n: Side}
local notation "X"=>Primary n G
local notation "ℓ"=>Measuring.chart n G
local notation "Y"=>Positions (Primary n G)
variable (G n)
noncomputable def sitePrice (G:Gauge)(n:Side)(t: Face (Per n))(x:Positions (Primary n G)):=G.price (faceValue (represent (tint G _ x)) t)
variable {G n}{t: Face (Per n)}
open MvPolynomial
variable (r:ℕ) {K:ℝ}
variable (h:PaintSupply G (r+2) K)
include h
noncomputable def stock (G:Gauge)(K:ℝ)(r:ℕ) := priceCost G (travelCost G (r+2) 4 (Uniform.composeCost (r+2) K (shade G)))
lemma onion (t:Face (Per n)): Lumber (Measuring.chart n G) t.1 4 (sitePrice G n t) (r+1) (stock G K r) :=by
    let f(v:Positions (Primary n G)):=represent (tint G _ v)
    have ht(i:Edge (Site n)) : Allows (r+2) (fun v : Y=> G.mat (f v i)) 0 (Uniform.composeCost (r+2) K (shade G)):=by
        let L:Y→L[ℝ]G.Color:= (ContinuousLinearMap.proj (i.1,Exterior.coord i.2)).comp (tint G _).toContinuousLinearMap
        have hx:‖L‖≤ shade G:=by apply L.opNorm_le_bound (shade_pos ..|>.le); exact fun x=> (norm_le_pi_norm ((tint G _) x) _).trans (tint_le x)
        have hb: ‖L 0‖≤ shade G:=by rw [map_zero,norm_zero]; exact shade_pos ..|>.le
        have hp(v:Y): G.mat (f v i) =G.mat (G.lieExp (L v)):=by unfold f; rw [Work.F03.represent_link];rfl
        simp_rw [hp]; exact (h.2 _ hb).comp (allows_linear hx hb)
    have hv: Allows (r+2) (sitePrice G n t) 0 (stock G K r):=by
        apply Allows.price (f:=fun v:Y=>faceValue (f v) t); exact travel_jets (U:=f) ht (w:=square _ _) t.1 (by simp [square])
    refine native (sitePrice G n) t _ _ _ _ _ (hv.1.of_le le_top) (hv.2 (r+2) le_rfl) (Filter.Eventually.of_forall fun x=> ?_)
    let v:=haul X (curbL ℓ t.1 4) x; change G.price (travel (f v) t.1 _)=_; refine congr_arg G.price (Uniform.path_same (G:=G) (w:=square t.2.val.1 t.2.val.2) ?_); intro i he; unfold f; rw [Work.F03.represent_link, Work.F03.represent_link]; apply congr_arg; ext k
    let j:=primary i k; change v j=x j; unfold v haul; rw [if_pos]; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩; rw [separation_comm]; exact he -- simp only [square,List.length_cons,List.length_nil] using he
variable {a:ℝ}{s:ℕ}
noncomputable def duty (G:Gauge)(K:ℝ)(a:ℝ)(s r:ℕ):= cities (Fintype.card PlaqAxes) 4 * rugL a (stock G K r) s 4 (r+1) (cities (tintCost G) 4)
lemma earned(ha:0≤a)(he:0<r): Tokew (Measuring.chart n G) a s (r+1) 0 (Parma.teethT (Rolling.opening G n) r) (duty G K a s r):=by
    let S:=sitePrice G n; let t:=Parma.teethT (Rolling.opening G n) r
    have hv(i:Face (Per n)):= onion r h i; let v:= potter (widthV G n) (r+2)
    have ht: t= -v:=by unfold t Parma.teethT opening; rw [map_neg,splitV,map_sub,PowerSeries.coeff_C_of_ne_zero he.ne',sub_zero, singularity,PowerSeries.coeff_mk]
    have hp := scaleBook (l:=ℓ) (p:=s) S hv (hv (Classical.arbitrary _)).1 ha (widthV G n) (Eventually.of_forall fun x=>rfl) _ _ (starM G n) (powerP n PlaqAxes) (r+1) -- p
    change Tokew _ _ _ _ _ t _; rw [ht,← neg_one_smul ℝ]; apply (Tokew.delta (hp.smoky (-1))); exact le_rfl; unfold duty tintCost; simp
-- seed width.F. enough eventual∀ j gr.Clock.
lemma pursue (hp:0≤ a)(he:0<r)(t:ℝ)(i:ℕ)(hv:1 ≤ t)(hL:duty G K a s r*t^(r+1+1) ≤ t^i): Tin (Measuring.chart n G) a s (r+1) t (teethT (opening G n) r) (t^i):=by
    have hw:0<t:=zero_lt_one.trans_le hv; exact (Tin.lit hw hv (earned r h hp he (n:=n))).it hw ((mul_comm ..).trans_le hL) le_rfl
end YM.MSbar.Alto
