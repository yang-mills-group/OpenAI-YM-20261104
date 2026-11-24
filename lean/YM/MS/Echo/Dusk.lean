import YM.MS.Echo.Wisp
/-!
# On the actual (cover) logarithmic heat end including scalar limit
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Osc.Snap Native Fiddle
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Flux City Signal Modeled Frame Wire Latch Job Belt Rake Orbit Orbit.LogReal Vista High.Knobs Fleet Rake.Geo
open scoped Topology ContDiff Interval
variable {G:Gauge}{n i k:ℕ}{ φ: Actor G}{u:ℤ}{X F:Dec G}{p:Team}{R: High.Recount G}
variable (x:ℝ)
local notation "ΩV"=> rel x
variable (B: Fixed ( col ( skyline G p )) R true 4 1)(K:Circle G φ false u)(H:PM φ ( skyline G p ) F u)
local notation "Φ"=> skyline G p
local notation "ζ"=> ratioF x
local notation "P"=> stout x * ratioF x
lemma sustan (f:SpanT): 0≤ζ f:= pay_m ..
lemma ρpos : nn (stout x*ratioF x):= joy ( he_zero x ) ( sustan x )
lemma proper_ζ (i:SpanT): ζ i=huge x i ^ (-eps_gain):=rfl
include B K H
lemma pulse_m (i:ℕ): Lease false false ΩV ( fun p=>orbit (capU G p) μzone ( keeping x ( F i ) p )) P:= by simp_rw [ attach1 x (H.owes i) ]; exact planC (mantle x B K H) ( planetV x ) (Tall _ 5 (by omega)) (fun E _=>tom _ _ (by omega)) ( sustan x ) ( he_zero x )
lemma regularV (n k:ℕ): Lease false false ΩV ( fun p=> tree parity (capU G p) ( keeping x ( Φ n ) p ) ( keeping x ( F k ) p ) ) P:= by
   by_cases he: n=0; · obtain hp:Φ n=0:= he.symm ▸ ( skyPC .. ).free; rw [hp, show (fun _=>tree _ _ ( keeping x 0 _ ) _)=0 from funext (fun i:SpanT=>LinearMap.congr_fun ( ( boulevard parity ( capU G i ) ).map_zero ) ( F k x i.val )) ]; exact Lease.zero (ρpos x)
   obtain he:0<n:= Nat.pos_iff_ne_zero.mpr he; obtain ht:= SpaceOut.sky_budget (ηv x) (skyPC G p) B -- signature includes L?
   let r(i:SpanT):= (ΩV).length i ^ ( -(4:ℝ) ); obtain hz: Lease true true ΩV ( keeping x ( Φ n ) ) r:= by
       apply νtransfer x ( d:=4 ) ?h; have h:= ht n he; unfold χr at h; simpa only [ ← good_η ] using h
   refine Lease.sticks ( S:=ΩV ) ( trunks ( planetX x ) hz ( mantle x B K H ) (he_zero x) ( fun i=>Real.rpow_nonneg ((ΩV).pos i).le _ ) ( sustan x ) ) ( fun i=> le_of_eq ?_ ); simp only [positive,r, Pi.mul_apply]; rw [Real.rpow_neg ( ( ΩV ).pos i|>.le ), show (ΩV).length i ^ (4:ℝ)= _ from Real.rpow_natCast ( ( ΩV ).length i ) 4 ]; field_simp [ (ΩV).pos i|>.ne' ] -- Pi F etc
lemma eat (i:ℕ) : paid ΩV (fun f:SpanT=> ‖res Φ F x f.val i []‖ ) P:= by
    let U:SpanT→ Law G:= fun p=>orbit (capU G p) μzone ( keeping x ( F i ) p ) + ( ∑ j∈antidiagonal i, tree parity (capU G p) ( keeping x ( Φ j.1 ) p ) ( keeping x ( F j.2 ) p ));
    have hV(p:SpanT): res Φ F x p.val i [] = U p []:= by
       unfold U res GridR.res Ω; simp only [ promised,paired, LinearMap.add_apply, Finset.sum_apply,Pi.add_apply,Z, rack, blvd ]; simp [ Charge.raise, payR,capU ]
    simp_rw [ hV ]; let X (p:SpanT):=∑ j∈antidiagonal i, tree parity ( capU G p ) ( keeping x ( Φ j.1 ) p ) ( keeping x ( F j.2 ) p ); obtain he : Lease false false ΩV U P:= Lease.plus ( g:=X ) (pulse_m x B K H i) ( Lease.sum _ (fun j _=> regularV x B K H j.1 j.2) (ρpos x)); obtain ⟨C,hC,k,hk⟩:= ( he ℝ [] (fun v=> Bool.noConfusion v) (fun v=> Bool.noConfusion v) ).norm_cost; exact ⟨ C,hC,k,fun i=> by convert hk i 0 trivial using 1; rfl; simp [pitch,fieldDim,Scale.full,Scale.weight] ⟩
omit B K H in
lemma tail (g:ℝ→ℂ)(hp:paid ΩV (fun i:SpanT=>‖g i‖) P): Tendsto g atTop (𝓝 0):= by
    obtain ⟨C,hC,k,hk⟩:= hp; let f(t:ℝ):=(1+log (1+max 1 t))^k* (max 1 t)^(-eps_gain ); let h0(t:ℝ): 1≤max 1 t:= le_max_left ..; obtain hT:Tendsto f atTop (𝓝 0):= timeW ( f:=atTop ) (Filter.tendsto_atTop_mono ( g:=fun t:ℝ=>max 1 t ) (fun i=> le_max_right ..) tendsto_id ) h0 _ p_gain k; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ ( ( by simpa using hT.const_mul (C*(1+|x|)^k) ) : Tendsto (fun t=> C*(1+|x|)^k*f t) atTop (𝓝 0)); filter_upwards [eventually_ge_atTop (1:ℝ)] with i hi; let p:SpanT:=⟨ i,hi ⟩; have hx:= hk p; rw [Pi.mul_apply] at hx; refine hx.trans ?_ -- unfolding failed
    unfold f; rw [ hf x p, proper_ζ, stout, huge,future, max_eq_right hi,mul_pow ]; dsimp only [p]; have he:=log_nonneg (show 1≤1+i from (by linarith)); have ht:(1+|x|)>0:=by positivity
    calc
       _ ≤ C*(((1+|x|)^k) * ((1+ log (1+i))^k))*(1*i^(-eps_gain)):= by gcongr; exact inv_le_one_of_one_le₀ hi
       _ = _:= by ring
lemma clock0 (i:ℕ) : Tendsto (fun t=> res Φ F x t i [] ) atTop (𝓝 0):= tail x _ ( eat x B K H i )
end YM.MS.Echo
