import YM.RegulatorIR.Binding.Terminal
import YM.RegulatorIR.Binding.Pen

/-!
# Landscape for inversion-regulated *finite coefficient* theorem

At each step same finite horizon external spins. H gauge data credited by
congruence for full origin/resetting germ. This formal comparison uses auxiliary
invertible ratios of the positive-branch coupling germ (may be realized by many
functions away from t=0). Costs don't tune a coupling. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Tree Series Series.Radial
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {I J E L:Type} [Fintype E][Fintype I][Fintype J][Fintype L]
variable {c f:Side}

structure Viewport (G:Gauge)(I:Type) where
 room : RoomK G I→ Prop
 cog : Meadow G I→ Prop

def full (G:Gauge)(f:Side) : Viewport G (OEdge f):=⟨Flat G f, GradientSite⟩
def door (G:Gauge): Viewport G Empty:=⟨fun _=> True, fun _=>True⟩

-- Parametric stationary landscape. Read along external coupling rays and V. Need G-cost smooth + quad angle.
-- continuity of F generally fails; require exact triangulated location clause.
structure Stead (P:Viewport G I)(F: Hook G E I) : Prop where
 seen : Measurable (fun x:ℝ × RoomK G I × RoomK G E=> F x.1 x.2.1 x.2.2)
 nonneg : ∀ t x y, 0≤ F t x y
 localK : Stationary (priceMap F)
 whereR (r : ℕ → ℝ) (x:ℕ→ RoomK G I) (u:ℕ→ RoomK G E) (X W) : Tendsto r atTop (𝓝 0) → Tendsto x atTop (𝓝 X) → Tendsto u atTop (𝓝 W) → Tendsto (fun i=> F (r i) (x i) (u i)) atTop (𝓝 0) → P.room X ∧ (X=1→ W=1)
 scope : ∀ Z:Meadow G E × ℝ × Meadow G I, 0≤ jet (priceMap F) 2 Z ∧ (jet (priceMap F) 2 Z=0 → P.cog Z.2.2 ∧ (Z.2.2=0 → Z.1=0))
-- O derivative any polynomial Laurent cutoff supplied. no positivity or integral here
structure Tune (A:Hook G E I) : Prop where
 view : Continuous (fun p:ℝ × RoomK G I × RoomK G E=> A p.1 p.2.1 p.2.2)
 smooth : ContDiffAt ℝ ∞ (priceMap A) 0
lemma shapeOne : Tune (1: Hook G E I):= ⟨continuous_const,contDiffAt_const⟩
namespace Stead
lemma allows {P:Viewport G I}{F A:Hook G E I}(h:Stead P F)(F':Tune A) : Bundle F A:=by
 refine ⟨h.seen, h.nonneg,F'.view,?_, fun r y z v hr hy hz hb => (h.whereR r y z 1 v hr hy hz hb).2 rfl⟩
 refine ⟨h.localK,fun x hx=> lt_of_le_of_ne (h.scope (x,0)).1 (fun hg=> hx (((h.scope (x,0)).2 hg.symm).2 rfl)),?_⟩
 exact F'.smooth.mul ((Chart.Ratio.jacobian_smooth (U:=E) (Orb.traySpec G)).of_le le_top |>.comp (f:=Prod.fst) (0:Meadow G E × ℝ × Meadow G I) contDiffAt_fst)
end Stead

structure Transfer (I L : Type)(G:Gauge) where
 inlet : RoomK G L→ RoomK G I
 curve : Meadow G L →ₗ[ℝ] Meadow G I
 invariant : ∀ x,inlet (expLinks G L x)=expLinks G I (curve x)
 continuous : Continuous inlet

-- Y(current) group viewport J. scroll T whereas aperture generates chart
structure Move (P:Viewport G I) (Q:Viewport G J)(V: Transfer I L G)(F:Hook G L J): Prop where
 seen : Measurable (fun x:ℝ × RoomK G J × RoomK G L=> F x.1 x.2.1 x.2.2)
 nonneg : ∀ t x y,0 ≤ F t x y
 localK : Stationary (priceMap F)
 whereS (r : ℕ→ℝ)(y:ℕ→RoomK G J)(z:ℕ→ RoomK G L)(Y W) : Tendsto r atTop (𝓝 0)→ Tendsto y atTop (𝓝 Y)→ Tendsto z atTop (𝓝 W) → Tendsto (fun i=> F (r i) (y i) (z i)) atTop (𝓝 0) → P.room (V.inlet W) → Q.room Y ∧ (Y=1→W=1)
 sphere : ∀ z:Meadow G L × ℝ × Meadow G J, 0≤jet (priceMap F) 2 z ∧ (jet (priceMap F) 2 z=0→ P.cog (V.curve z.1) → Q.cog z.2.2 ∧ (z.2.2=0 → z.1=0))

-- Standalone stationary rays. For proving sum and step Hessians.
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
def fees (f:X→ℝ)(r:ℝ)(z:X):= f (r • z)/r^2
lemma jets_cap (f:X→ℝ)(h:ContDiffAt ℝ ∞ f 0)(z:X)(k:ℕ): jet f k z= (k.factorial:ℝ)⁻¹ * iteratedDeriv k (fun t:ℝ=> f (t • z)) 0 := homogeneous_derivative f z k (h.of_le (WithTop.coe_le_coe.mpr le_top))
lemma smoothed (f:X→ℝ)(h:ContDiffAt ℝ ∞ f 0)(z:X): ContDiffAt ℝ 2 (fun t:ℝ=> f (t • z)) 0:= ((show ContDiffAt ℝ ∞ f ((0:ℝ) • z) from (show (0:ℝ) • z=0 from zero_smul ..) ▸ h).of_le (m:= (↑(2:ℕ):WithTop ℕ∞)) (WithTop.coe_le_coe.mpr le_top)).comp 0 (contDiffAt_id.smul contDiffAt_const)
lemma due (F:X→ℝ)(h:Stationary F)(x:X): Tendsto (fees F · x) (𝓝[≠] (0:ℝ)) (𝓝 (jet F 2 x)):=by
 let g:=fun r:ℝ=> F (r • x)
 have he:g 0=0:=by unfold g; rw [zero_smul,h.base0]
 have ht: deriv g 0=0:=by
    have hp:=h.base1 x; rw [jets_cap F h.smooth x,iteratedDeriv_one] at hp;simp at hp;exact hp
 convert Work.F03.taylor_limit_two (smoothed F h.smooth x) he ht using 1 <;> try rfl
 rw [jets_cap F h.smooth]; apply congr_arg; norm_num [Nat.factorial];ring
lemma declares (F:X→ℝ)(h:ContDiffAt ℝ ∞ F 0)(h₁:∀ x:X,∃ c,Tendsto (fees F · x) (𝓝[≠] (0:ℝ)) (𝓝 c)): Stationary F:=by
 have hp (x:X) : F 0=0 ∧ jet F 1 x=0:=by
    obtain ⟨c,hc⟩:= h₁ x
    obtain ⟨ht,hq⟩:=Work.F03.value_slope_of_sq_limit (smoothed F h x|>.continuousAt) hc
    refine ⟨by simpa using ht,?_⟩
    rw [jets_cap F h,iteratedDeriv_one,hq.deriv,mul_zero]
 exact ⟨h,(hp 0).1,fun _=>(hp _).2⟩
end YM.RegulatorIR.Binding
