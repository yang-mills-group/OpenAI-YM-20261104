import YM.RG11Scheme.Stencil.Many
import YM.Pert.Align.Span

/-! List concrete directional monomials spanning the leading stencils. Exact all-link identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4800
namespace YM.RG11Scheme.Stencil.Point
open Filter Function Set Lattice Mesh Maxwell Pert Align Align.Atom Spark Bare
open Stencil.Cell
open scoped BigOperators Classical
variable {G:Gauge} {D:Type*} [AddCommGroup D][Module ℝ D] {j d:ℕ}
local notation "Δ" => Bond G
structure Chip (G : Gauge) (j:ℕ) where
   aim:link
   u:G.Color
   d : List Axis
   len : d.length=j

noncomputable def tip (v:G.Color) : Δ → Axis → Cover → ℝ := fun f i x=> inner ℝ v (f (x,i))
def stub (K:Chip G j) : Dual G where
   toFun X := go K.d (tip K.u X K.aim.2) K.aim.1
   map_add' X Y := show _ by rw [show tip K.u (X+Y) _= tip K.u X _ + tip K.u Y _ from funext fun x=> (inner_add_right ..),plus_go]
   map_smul' r X := by
      change go K.d (tip K.u (r • X) _) K.aim.1 = r * _
      rw [show tip K.u (r • X) _=(fun x=> r * tip K.u X _ x) from funext fun x=> real_inner_smul_right ..]
      exact go_map (AddMonoidHom.mulLeft r) _ _ _
def quarry (G:Gauge)(d:ℕ) := Submodule.span ℝ (Set.range (stub (G:=G) (j:=d)))
def periscope (p:Pad G j) (s:Signed) : Dual G := p ∘ₗ wideCore G j (affine s⁻¹ 0 (0:Cover)) ∘ₗ wideLink G s

def mine (a:Align.Atom j)(v:G.Color) : Chip G (j+1) := ⟨(a.foot true,a.rotated),v,a.dirs,a.length_dirs⟩
lemma flashes (A:Align.Atom j) (v:G.Color)(X:Δ): inner ℝ v (A.readK X 0)= A.factor * (stub (mine A v) X):= by
   rw [tuned,real_inner_smul_right]
   apply congrArg; change _=go A.dirs _ _; exact (go_map ((innerSL ℝ v).toLinearMap.toAddMonoidHom) (fun y:Cover=> X (y,A.rotated)) _ _).symm
lemma meter_frames (v:Align.Spot G j)(s:Signed) : periscope v.meter s ∈ quarry G (j+1) := by
   let A:=v.atom s
   let B:Align.Atom j:= {A with slash:=A.channel, channel:=A.slash}
   let u:=unitColor G v.color
   let P:=quarry G (j+1)
   have hx: periscope v.meter s=(j.factorial:ℝ)⁻¹ • (A.factor • stub (mine A u)-B.factor • stub (mine B u)) := LinearMap.ext (fun X=>by
      rw [periscope,v.meter_atom s]; change inner ℝ u (wideCore G j (affine A.rot⁻¹ 0 (0:Cover)) (wideLink G A.rot X) A.slash A.channel A.γ)=_
      rw [A.core_combine,real_inner_smul_right,inner_sub_right, flashes, flashes B]; rfl)
   rw [hx]
   have hi (A:Align.Atom j) : stub (mine A u)∈P := Submodule.subset_span (mem_range_self _)
   exact P.smul_mem _ (P.sub_mem (P.smul_mem _ (hi A)) (P.smul_mem _ (hi B)))
lemma periscope_at (p:Align.Pad G j)(s): periscope p s∈ quarry G (j+1) := by
   let Q := Align.pickDual (wideCore G j (affine s⁻¹ 0 (0:Cover)) ∘ₗ wideLink G s)
   change Q p∈_
   nth_rw 1 [Align.pad_full p]; rw [map_sum]
   have he (a:Align.Spot G j) : (p a.impulse • a.meter) ∘ₗ ((wideCore G j (affine s⁻¹ 0 (0:Cover))) ∘ₗ (wideLink G s))= p a.impulse • periscope a.meter s:= LinearMap.ext fun _=> rfl
   apply Submodule.sum_mem; intro c _; change ((p c.impulse) • c.meter) ∘ₗ (wideCore G j (affine s⁻¹ 0 (0:Cover)) ∘ₗ wideLink G s) ∈ quarry G _; rw [he]; exact (quarry G _).smul_mem _ (meter_frames c s)
lemma takeoff (h:ℝ)(p:Scalar G j): forward p 0 h ∈ quarry G (j+1) := by
   let U (s:Signed):=periscope (p ∘ₗ outside h s j) s
   have he : forward p (0:Cover) h=(Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,U s := LinearMap.ext (fun X=>by rw [forward,LinearMap.comp_apply,sided,p.map_smul,_root_.map_sum,LinearMap.smul_apply,LinearMap.sum_apply]; simp only [U,periscope,LinearMap.comp_apply])
   rw [he]; apply (quarry G _).smul_mem; apply Submodule.sum_mem;intro s _; exact periscope_at (p ∘ₗ outside h s j) s
end YM.RG11Scheme.Stencil.Point
