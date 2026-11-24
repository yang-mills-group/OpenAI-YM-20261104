import YM.MS.Swirl.Sro
/-!
# Unnormalized moment of a normalized heat flow and limits
Works for ALL gauges (Sector function includes ghosts). Θ true.Brightness root Unit.
Projection dropped later to simplify wave theorem. Λ fixed lattice formulation. Includes any arity-labeled
pure.HP in source geometry through Mom and sym.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Orbit Cog Orbit.LogReal Book Convolve Program Puff Engine SplitP Actors Dynamics Puff.Mom
open scoped Topology ContDiff Interval
variable {A I W:Type}{p:Sector A}{X:LogReal.Series A}{L P:Lines A}{K: Grain A}{U: Series A}{Q V: SpecB A}{n:ℕ} [Fintype A]
-- unnormalizing exp(log) Θ
variable (he:∀ t, Clear p (L t)) (hX: Background p L Q X)(hx:∀ i,Pure p false ( Q i ))
    (hp:Lodged p L X V U)(ht:U∈(StackP p).guard)
local notation "M"=> Pie p
local notation "Mτ"=> StackP p
local infix:70 " ⋆ "=> Actors.core ( Mτ )
local notation "Ξ"=> tintB p X
local notation "σ"=> useN
local notation "W0"=> ( Mote he )
set_option quotPrecheck false
local notation "Φ"=> ( W0 ).liftV useN
local infix:70 " ★ "=> Actors.core ( PermV p )
include he hx hX ht
lemma realize : (Φ).join U Ξ= ((Φ).join U X) ⋆ Ξ:= by
   let h:= branchB he hX hx; let K':= Φ; have hm (n:ℕ): ( Φ ).join U ((Mτ).cheers X (n+1))= ( Φ ).join U X ⋆ ((Mτ).cheers X n):= by
       unfold cheers; rw [map_sum,map_sum,Finset.sum_range_succ', firstW,(Φ).simple ht,add_zero ]; exact Finset.sum_congr rfl fun i _=> join_wage K' X h i U ht
   have hv (n k:ℕ)(he:n≤k): ( Mτ ).cheers X k n= Ξ n:= overbook M σ X hX.1 ( n:=k ) he; -- grade defeq
   let H x:= (Mτ).cheers X x;
   funext n; have Ht (L: Angled (OM A))(F:Series A)(k:ℕ)(hh:n≤k): useN.Lift L F Ξ n=useN.Lift L F (H k) n:= by rw [useN.loan,useN.loan]; apply Finset.sum_congr rfl; intro j hj; obtain hp:= Finset.mem_antidiagonal.mp hj; rw [← hv j.2 k (by omega)]; -- binder hh
   rw [ show (Φ).join _ _ _=useN.Lift (W0).join U Ξ n from rfl, Ht (W0).join U (n+1) (by omega) ]; rw [show ( _ ⋆ _ ) n= useN.Lift (M).core ( (Φ).join U X ) Ξ n from rfl, Ht (M).core _ n le_rfl ]; exact congr_fun ( hm n ) n
include hp
abbrev fire (t:ℝ)(A:Type): Linear ( LogReal.Series A ) (SpecB A):= pointL ℕ ( LinearMap.proj (R:=ℂ) t )
abbrev exp0 (p:Sector A)(Q:SpecB A):= Cheer ( actor p ) useN Q
local notation "sB"=> exp0 p Q
local notation "Fx"=> ( HeatFlow.deriv p ).extrapolate useN
omit hp ht hx he in
lemma sB0 (hz:Q 0=0): fire 0 A Ξ=sB:= by
   have hv : LinearMap.proj ( R:=ℂ ) (0:ℝ) ∘ X=Q:= by
       funext n; by_cases hm:0<n; · exact hX.2 n hm|>.1
       change X n 0= _; rw [ show n=0 from (by omega), hz,hX.1 ]; rfl
   funext i; obtain he:=(rain ( «M»:=actor p ) ℝ 0).figure useN X i; rw [hv] at he; exact he
omit [Fintype A] he hx hX ht hp in
lemma fireΩ (t:ℝ): Tether (fire t A) Mτ (PermV p):= ( rain ℝ t ).Extrapolation useN
lemma ignition (hv:Q 0=0): ( Fx ).valid ( Ξ ⋆ U ) (( Φ ).move ( Ξ ⋆ U )) ∧ fire 0 A ( Ξ ⋆ U )= sB ★ V := by
   have hb : Ξ∈ ( Mτ ).guard := Cinch.totalZ (P:=useN) ( branchB he hX hx ); obtain hB : (Fx).valid U (( Φ ).move U+ ( Φ ).join X U):= fun i=> by change Status _ ( Static L _+ (Φ).join X U i ); rw [ leafN he hX ]; exact (hp i).2
   obtain h : (Fx).valid Ξ ( (Φ).move Ξ ):= point_ξ he hX hx
   refine ⟨ ?_,?_⟩; · rw [(Φ).compatibility _ _ hb ht]; convert ( Fx ).duop _ _ _ _ h hB using 1; rw [map_add,(Φ).rear hb ht, realize he hX hx ht,(Φ).rear ( branchB he hX hx ) ht,(Mτ).turns Ξ hb ((Φ).join U X) ( ( Φ ).join_close ht ( branchB he hX hx ) ) ]; abel
   rw [ fireΩ 0|>.craft, sB0 hX hv, show fire 0 A U=V from funext fun i=> hp i |>.1 ] -- args
-- rewrite Orth.Status
omit he hx hp ht
omit hX
lemma boost (V0: SpecB A)(U:Series A){K:Lines A}(h:∀ i,Status ( U i ) (Static K ( U i )))(hv:fire 0 A U=V0)(i:ℕ): Fill K (V0 i) (U i) 0:= ⟨ congr_fun hv i, by rw [add_zero]; exact h i⟩
-- debating scalar endpoint
variable {V': SpecB A}{g:T ℂ}{μ:ℝ→ BL A}
abbrev Z_Actual (V: Series A)(x:T ℂ): Prop:= ∀ i,Tendsto (fun t=> V i t []) atTop (𝓝 (x i))
local notation "ρ"=> ℶV K
local infix:70 " ⚘ "=> Actors.core Trunk
local notation "Z"=> ρ sB
omit [Fintype A] in
lemma calumni (he:Z_Actual U g){f:T ℂ}(hp:Z_Actual X f): Z_Actual ( U ⋆ X ) ( g ⚘ f ) := by intro i; change Tendsto (fun t=> ( (∑ p'∈ antidiagonal i,( M ).core ( U p'.1 ) ( X p'.2 )) _ ) []) atTop _; simp_rw [ Finset.sum_apply ]; exact tendsto_finsetSum (antidiagonal i) (fun b _=> ( ( he b.1 ).mul ( hp b.2 ) ).congr (fun _=> Eq.symm (times_nil ..)))
variable (hW: Wellness p P L K)(hG:Γ Q p) (hz: Q 0=0)
include he hx hX hW hG hz
lemma ℶβ : Z_Actual Ξ Z := by
   have hf: ∀ i, Fill L (sB i) (Ξ i) 0:= boost _ _ ( point_ξ he hX hx ) ( sB0 hX hz ); exact fun i=> hW.riseΩ ( hf i ) ( expΓ hG i (Set.mem_univ _ )) -- pointL ℕ Fee S
include hp ht
lemma reg_Lη (he': Γ V p)(h: Z_Actual U g): ρ ( sB ★ V )= Z ⚘ g:= by
   obtain ⟨hβ,hz'⟩:= ignition he hX hx hp ht hz; have hc := calumni ( p:=p ) ( ℶβ he hX hx hW hG hz ) h; exact funext fun t=> tendsto_nhds_unique ( hW.riseΩ ( boost _ _ hβ hz' t ) ( ΤΓ_pair (expΓ hG ) he' t ( Set.mem_univ _ ) ) ) ( hc t ) -- cast ∇
end YM.MS.Swirl
