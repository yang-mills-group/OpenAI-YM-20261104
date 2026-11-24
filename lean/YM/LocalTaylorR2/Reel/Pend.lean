import YM.LocalTaylorR2.Unroll
import Mathlib.Order.Filter.Germ.Basic
import YM.FullVolume.Panel.Beach
import YM.LocalTaylorR2.Reel.Spins
/-! Preserve germs for integrator -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Port RG01.Survive PhysicalNext PhysicalNext.Repeat Greenbelt
variable {k : ℕ} {p : Molecule S}
section tripod
-- to compare at boundary of good mask; only eventual equality available
variable {X:Type*}
lemma glassRight {P Q:Config G c→X} {U:Config G c} (h:P∘increment U=ᶠ[𝓝 0] Q∘increment U): P=ᶠ[𝓝 U] Q:= by
   let f (i:Bond c) (W:Config G c):= W i*(U i)⁻¹; let d (W:Config G c) (i: Edge (Site c)):= G.plog (G.mat (f i W))
   have he i : Tendsto (f i) (𝓝 U) (𝓝 1):= by simpa [f] using! (show Continuous (f i) by unfold f; fun_prop).tendsto U
   have hp : Tendsto d (𝓝 U) (𝓝 (0:Directions G c)):= by
     apply tendsto_pi_nhds.mpr; intro i
     change Tendsto (G.plog ∘ G.mat ∘ f i) _ (𝓝 0)
     rw [← G.plog_one]; exact G.plog_diff.continuousAt.tendsto.comp ((G.continuous_mat.tendsto _).comp (he i))
   filter_upwards [h.comp_tendsto hp,eventually_all.mpr (fun i=> (he i).eventually G.plog_right)] with W hw hh
   have hh : increment U (d W)=W:= by ext1 i; change G.lieExp (d W i) * U i=_; rw [show G.lieExp (d W i)=f i W from hh i]; simp [f,mul_assoc]
   simpa only [Function.comp_apply,hh] using hw
abbrev Still {X:Type*} [TopologicalSpace X] (U:X):= Filter.Germ (𝓝 U) ℝ
def memo {X:Type*} [TopologicalSpace X] (U:X): (X→ℝ) →+* Still U:= Filter.Germ.coeRingHom (𝓝 U)
lemma memoScale {X:Type*} [TopologicalSpace X] (U:X)(a:X→ℝ)(c:ℝ):memo U (c•a)=c•memo U a := rfl
lemma line_eq {X:Type*} [TopologicalSpace X] (U:X)(a b:X→ℝ): memo U a=memo U b ↔ a=ᶠ[𝓝 U] b:= Filter.Germ.coe_eq
lemma scalar_prod {X:Type*}[TopologicalSpace X](U:X)(c d:ℝ) (x y: Still U): (c • x)*(d • y)=(c*d)•(x*y):= by
   induction x using Filter.Germ.inductionOn with | _ x => ?_
   induction y using Filter.Germ.inductionOn with | _ y => ?_
   exact congr_arg (memo U) (show (c•x)*(d•y)=(c*d)•(x*y) from funext fun i=> by simp only [Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; ring)
end tripod
section Population
variable {U:Support c}
open Kept
lemma plural {u v:Port.Test T} (h:Port.Kept H U u)(he:Kept H U v): Kept H U (u+v) := by
  constructor
  · intro F X X' w v hh h' Z hZ hv hp; exact congr_arg₂ (·+·) (h.links F X X' w v hh h' Z hZ hv hp) (he.links F X X' w v hh h' Z hZ hv hp)
  · intro _ _ F X hx hX V Y w hp h' ht; exact (h.borel _ _ _ hx hX _ _ _ hp h' ht).add (he.borel _ _ _ hx hX _ _ _ hp h' ht)
  · intro F X hx hX hΨ z w; exact congr_arg₂ (·+·) (h.rotate F X hx hX hΨ z w) (he.rotate F X hx hX hΨ z w)
  intro F X hx hX he' j b d E _ _ _ V x hp ht hw
  exact (h.clutch F X hx hX he' j b d E V x hp ht hw).together (he.clutch F X hx hX he' j b d E V x hp ht hw)
def Pop (H:Cash W s μ L Q o C T R)(A:Support c): Submodule ℝ (Port.Test T) where
    carrier := {x| Kept H A x}
    zero_mem' := Kept.fixed _
    add_mem' := @plural _ _ _ _ _ _ _ _ _ _ _ _ _ _ H A -- edit
    smul_mem' := fun x _ h=> (Kept.fixed x).times h
lemma popPow (_H:Cash W s μ L Q o C T R)(x y:ℝ)(a b:Port.Test T) : (x • a)*(y • b)=(x*y) • (a*b):=by ext F X w; change x*_*(y*_)=x*y*(_*_); ring
lemma likely_scale {α:Type} [Fintype α] (F:α→ℝ) (x:ℝ): Pond.likely (fun i=>x*F i)=x*Pond.likely F:=by unfold Pond.likely; rw [← Finset.mul_sum]; ring
lemma scaleFrame (X:Coat T F)(U:Support c)(q:Port.Test T)(c':ℝ): Port.onFrame X p U (c' • q)=c'*Port.onFrame X p U q:= by
   let X' t:= (preps X (roster p)).taggedL t; let I := podium S G U X.B
   have h t:Port.average (X' t) I (c' • q)=c'*Port.average (X' t) I q:= by
      unfold Port.average; rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with Y
      rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with i; dsimp only [Pi.smul_apply,smul_eq_mul]; ring
   unfold Port.onFrame; unfold X' I at h; simp_rw [h,likely_scale]
variable {χ:Chi}
lemma scaleCast (V:Config G c)(q:Port.Test T)(w:ℝ): episode H χ p (w • q) V=w*episode H χ p q V:=by
   unfold episode rinsed; simp_rw [scaleFrame,integral_const_mul,likely_scale]
variable {b' t u σ e y t' Z δ : ℝ} {n : ℕ}
variable (N:Captain H k b' t u σ e y t' Z δ n χ)
include N
lemma corn (V:Config G c)(q f:Port.Test T)(hq:Kept H (H.unionP p) q)(hf:Kept H (H.unionP p) f)(hv:Healthy (Pressure.temp s) (H.unionP p) V)(hz:(roster p).flags=∅) : memo V (episode H χ p (q+f))=memo V (episode H χ p q)+memo V (episode H χ p f):=by
   apply Filter.Germ.coe_eq.mpr; apply Reel.glassRight
   refine March.trust (j:=k) N.position (fun U h ht=>?_)
   have hF i : Kept H (H.unionP p) ((fun x:Bool=>if x then q else f) i):= by dsimp only; split <;> assumption
   have hy := Port.episodeSum (K:=q+f) (p:=p) (fun a X u=> (show (q+f) a X u=∑ i:Bool,(if i then q else f) a X u from by simp)) N.oboe hz h (plural hq hf) hF (ht.symm ▸ hv)
   filter_upwards [hy] with v hv; simpa only [Fintype.sum_bool,ite_true,ite_false,Bool.false_eq_true,Function.comp_apply] using hv
variable {θ:Type*}{w:θ → ℝ} {p' :ℕ} {f':θ → Port.Test T}
lemma pendulum (V:Config G c)(hv:Healthy (Pressure.temp s) (H.unionP p) V) (h0:(roster p).flags=∅) (h:Filled (Pop H (H.unionP p)) p' w f'):
    Filled ⊤ p' w (fun i=>memo V (episode H χ p (f' i))):=
    h.transfers (fun x=> memo V (episode H χ p x)) (fun _ _=> Submodule.mem_top) (fun x hx y hy=>Reel.corn N V _ _ hx hy hv h0) (fun a _ v=> by rw [show episode H χ p (v • a)= v • episode H χ p a from funext fun x=> Reel.scaleCast x a v]; exact memoScale ..)
end Population
end YM.LocalTaylorR2.Reel
