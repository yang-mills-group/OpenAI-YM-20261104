import YM.X.Tot.Federate
/-!
# Transport common-measure frame reading to Jam then View and mask shift correction exact. Algebra in public `scope`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}
local notation "μ"=> flow G n
variable (o:Site n)(A B C U:Curly G)(z:Cover)
lemma multi_rot : dress z (multi μ A B) = multi μ (dress z A) (dress z B):= by refine turn_mix _ A B (pointB z) _ ?_; rw [Fund.tilt]
lemma contributor : let x:=hairAt (G:=G) o; Tot.space μ A B C U=Tot.space sale (x A) (x B) (x C) (x U):= by intro x; refine perp _ _ _ _ _ (place o) _ ?_; exact (sale_self o).symm -- he direction
lemma pay_sym : let x:=hairAt (G:=G) o; majority μ U A B C= majority sale (x U) (x A) (x B) (x C):= hex _ _ _ _ _ (place o) sale (sale_self o).symm
-- no λ frame expected child φ unheated mass ∑near
lemma fire_p : milk μ (Tot.pillar G)= Tot.pillar G:= by unfold Tot.pillar; rw [map_sum]; simp_rw [color_fire]
abbrev EngineP (q:ℕ+)(G:Gauge) := vertexLift q (shape (G:=G) q)
variable (q) (χ:Floor R)(X Y Z: Billboard G q)(P: Foam G)(p:Fielding.Walk)
local notation "o'"=> side q k
local notation "Q"=> qu q G
local notation "ε"=>epsilon q k
lemma shape_jump (z:Site (side q k)): volS q k • EngineP q G k z = dress (lift z) (Tot.pillar G):= by
    rw [EngineP,viz_val]; unfold shape priceCo;rw [map_smul,smul_smul]; change (volS q k * Complex.ofReal (ε ^(-4:ℤ))) • _ = _; rw [volS, ← Complex.ofReal_pow, ← Complex.ofReal_mul, zpow_neg,zpow_ofNat,mul_inv_cancel₀ (pow_pos (epsilon_pos q k) _|>.ne'),Complex.ofReal_one,one_smul]
lemma bead_cast (h:∀ z∈(Floor.maskL q χ k).support,lift (wrap (side q k) z)=z):mask (G:=G) q χ k=∑ z:Site (side q k), Complex.ofReal (χ.s (spot ε (lift z))) • dress (lift z) (Tot.pillar G):= by
    unfold mask fireMask; rw [←lift_band _ h]; simp_rw [dress_fire,Tot.pillar,RCLike.real_smul_eq_coe_smul (K:=ℂ), Floor.masking,map_sum]; rfl
local notation "𝒫"=> EngineP q G
-- scalar intake of all when fire normalized
lemma gas_site (h:Site n) : Pulse.gas G n=∑ z:Site n, hairAt (z+h) (Tot.pillar G):= by
    unfold Pulse.gas; rw [Fintype.sum_prod_type]; simp_rw [Tot.pillar,map_sum]; let f(z:Site n):= ∑ p:PlaqAxes,hairAt z (vertex (G:=G) p); exact (Equiv.sum_comp (Equiv.addRight h) f).symm
lemma space_shape (z:Site (side q k))(A B C:Curly G): volS q k*Tot.space (Q k) A B C (EngineP q G k z)= Tot.space (Q k) A B C (dress (lift z) (Tot.pillar G)):= by rw [← shape_jump q z]; exact (space_scale _ A B C _ _).symm -- id grammar
lemma gas_qu (h:Site (side q k))(z:Site (side q k))(A B C:Curly G): Hinge.shock sale (hairAt (z+h) (Tot.pillar G) * (hairAt h (A*B*C)))=volS q k* Tot.space (Q k) (milk (Q k) A) (milk (Q k) B) (milk (Q k) C) (EngineP q G k z):= by
    have hZ:=tint h (lift z) (Tot.pillar G); rw [wrap_lift] at hZ; rw [← hZ,← map_mul, ← Fund.loc,space_shape,Tot.market, minus,minus,minus]; let f:= dress (lift z) (Tot.pillar G); have hh:f= milk (Q k) f:= by unfold f; simp only [qu, Fund.milked,fire_p]
    rw [show milk (-(Q k)) (dress (lift z) _)=f from (congr_arg (milk (-(Q k))) hh).trans (minus (Q k) f)]; unfold f; simp only [mul_assoc]
lemma basin_shock (h:Site (side q k))(A B C : Curly G) : Hinge.shock sale (Pulse.gas G (side q k)* (hairAt h (A*B*C))) = crow q (fun t z=> Tot.space (Q t) (milk (Q t) A) (milk (Q t) B) (milk (Q t) C) (EngineP q G t z)) k:= by
    let L:= LinearMap.mulRight ℂ (hairAt h (A*B*C)); change Hinge.shock sale (L (Pulse.gas G o'))=_; rw [gas_site (h:=h),map_sum,map_sum,crow,Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; exact gas_qu q h z A B C
end YM.PositionX.Tot
