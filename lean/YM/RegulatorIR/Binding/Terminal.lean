import YM.RegulatorIR.Binding.Gauges
import YM.PertExtension.OrbHaar

/-! Terminal positive lump uses the full inversion-tree packing, not block
packing. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding.Last
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Precision
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {f :Side}{G:Gauge}

def inhabit : Meadow G (Cotree f) →ₗ[ℝ] Horizon G f where
 toFun:= genJet
 map_add' x y:=by funext i; rw [Pi.add_apply]; unfold genJet;split_ifs <;> simp
 map_smul' r x:=by funext i;rw [Pi.smul_apply];unfold genJet;split_ifs <;>simp
lemma boots (x:Meadow G (Cotree f)) : splitLink 1 (expLinks G _ x) = climb (inhabit x):=by
 ext1 i
 change (splitLink 1 _ i)= G.lieExp (genJet x i)
 unfold genJet splitLink; by_cases hp:Branch i <;> simp only [hp, dite_true, dite_false, not_true]
 · simp
 rfl
lemma fade : splitLink 1 (1:Cotree f → G.El)=1:=by ext1 i; unfold splitLink;split_ifs <;> rfl
lemma tone (G:Gauge)(f:Side): Continuous (splitLink (b:=(1:Trees f→G.El))):=by apply continuous_pi; intro i;unfold splitLink;split <;> fun_prop
lemma settle (x:Cotree f→ G.El)(hc: Even f.val)(h:Flat G f (splitLink 1 x)): x=1:=by
 apply flat_unique hc (G:=G)
 obtain ⟨k,hk,h⟩:=h
 have hv:= goat_lift k (splitLink 1 x) hk; rw [h, Geometry.lift_one] at hv
 change energy (orbLift (splitLink 1 x))=0
 rw [← energy_gauge _ k,← hv]; unfold energy;simp_rw [faceValue, anyWalk];simp

lemma still (x:Meadow G (Cotree f))(hc:Even f.val)(h:GradientSite (inhabit x)) : x=0:=by
 apply curl_gap hc; have ht:variation x= fire (inhabit x):= rfl; rw [ht]; exact grad_closed hc h
end YM.RegulatorIR.Binding.Last
