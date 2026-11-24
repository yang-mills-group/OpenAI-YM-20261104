import YM.OPE.Compatible.Arch.Vuln
/-!
# Rational recoil cost in local H chamber
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {I J:Type}{G:Gauge}[Fintype I]
open Radial Zone ScriptJ Metric
local notation "W" => Chart.tangent G I
local notation "N" => Module.finrank ℝ (Keys G I)
local notation "Lf" => Tested.germ
variable {P:ChartRatio G} (R: LocalRatio P)
-- patch convergence for recoil with Haar correction
structure Snap (f:ℝ→Tile G I→ℝ) (p:JetS ℝ):Prop where
   ready : ∃ s∈𝓝 (1:Tile G I),∀ d:Set (Tile G I),d⊆s→d∈𝓝 1→MeasurableSet d→ Reads (fun t=> peak (f t) d t) p
include R
lemma wind {f:Keys G I→ℝ}{g:ℝ→Tile G I→ℝ}(H:Radial.Stationary f)(hh:Measurable f)(Gm:∀ t,Measurable (g t)) {p:ScriptJ (Keys G I)} {A:ℝ→Keys G I→ℝ}(ha: Cape A p)(hA:∀ t,Measurable (A t))
     (hK:∀ᶠ y:Keys G I in 𝓝 0,∀ x t,0<t→ t•x=y→ Chart.jacobian P y*g t (put y)= A t x*Real.exp (-f y/t^2)) (ht:∃ c>0,∀ x:Keys G I,c*‖x‖^2≤jet f 2 x): Snap g (gemLift W (kernel f) (p*wheel (Pawn.mold f 2))):=by
      obtain ⟨c,hc,Ht⟩:=ht; let b:= c/2; have hb:0<b:=half_pos hc
      let a(t:ℝ)(x:Keys G I):=Real.exp (higher f t x); have he:Bears (shade b) (A*a) (p*wheel (Pawn.mold f 2)):=by simpa only [one_mul] using! ha.ascent (spender hb H)
      have hr: KernFit (kernel f) (b+b):=fun x=>⟨Real.exp_nonneg _, Real.exp_le_exp.mpr (by have hx:=Ht x; rw [show b+b=c by unfold b; ring]; nlinarith only [hx])⟩
      have hi(k:ℕ):Measurable (jet f k):=(Radial.Smooth.continuousJet ..).measurable
      have hV:Measurable (kernel f):=Real.measurable_exp.comp (hi 2|>.neg)
      have hv(t):Measurable ((A*a) t):=by apply (hA t).mul; unfold a higher; fun_prop
      refine ⟨satisfied R Gm he hv hr hb hV ?_⟩; filter_upwards [hK] with y hy x t ht he; rw [hy x t ht he]; simp only [Pi.mul_apply, kernel,a]; rw [mul_assoc,←Real.exp_add, ← he]; congr 2; unfold higher; ring
-- if both bear relative same numerator interpolation probe ratio
namespace JetS
instance : Inv (JetS ℝ) :=⟨fun p=>⟨(p.s)⁻¹,-p.l/p.s^2,p.l^2/p.s^3-p.h/p.s^2⟩⟩
instance : Div (JetS ℝ) :=⟨fun p d=> p*d⁻¹⟩
end JetS
abbrev riddle (u v:ℝ→Tile G I→ℝ)(d:Set (Tile G I))(t:ℝ):ℝ:= (∫ x in d,u t x ∂Gem G I)/(∫ x in d,v t x ∂Gem G I)
omit R in theorem meetQuota {u v:ℝ→Tile G I→ℝ} {p s:JetS ℝ}(a:Snap u p)(b:Snap v s)(ht:s.s≠0):∃ c∈𝓝 (1:Tile G I), ∀ d:Set (Tile G I),d⊆c → d∈𝓝 1→MeasurableSet d→ Reads (riddle u v d) (p/s):=by
     obtain ⟨c,hc,h⟩:=a.ready; obtain ⟨e,he,hp⟩:=b.ready; refine ⟨c∩e,inter_mem hc he,fun d hd ht₀ hh=>?_⟩; refine ((h _ (hd.trans inter_subset_left) ht₀ hh).pile ((hp _ (hd.trans inter_subset_right) ht₀ hh).invert ht)).cong ?_
     filter_upwards [Tested.eventually_pos] with x (hx:0<x); have he:x≠0:=hx.ne'; change riddle _ _ _ _=peak _ _ x*(peak _ _ x)⁻¹; unfold peak riddle; change _=((x^N)⁻¹*∫ a in d,u x a ∂Gem G I)*((x^N)⁻¹*∫ a in d,v x a ∂Gem G I)⁻¹; rw [← div_eq_mul_inv,mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero _ he))]
end YM.OPE.Libra
