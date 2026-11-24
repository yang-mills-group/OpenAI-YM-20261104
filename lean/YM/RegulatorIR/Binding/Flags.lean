import YM.RegulatorIR.Binding.Top
import YM.RegulatorIR.Ledger.Terminal

/-! Accumulated state of a certified *walk*. Includes exact equality to
unnormalized world-line/source event at top single purpose. Distinct from
calculation of represented cut-off density. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore Tree Tree.Forest Step
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge}{f c:Side}{I J L E:Type} [Fintype I][Fintype J][Fintype L][Fintype E]{r s m:ℕ}

-- Ratio theorem for normalized top functional. Unit before power; ∀ t.

-- allow integrand aspiration through any real t at each step because scale smooth.
structure RangeR (G:Gauge)(f:Side)(κ: Horizon G f→ℝ)(g:ℝ→ℝ) (s m:ℕ)(U V:Orders (Book G f)) where
  E:Type
  slots : Fintype E
  Val : Hook G E (OEdge f)
  Mark : Hook G E (OEdge f)
  scalar :PowerSeries ℝ
  basis : @Stead G (OEdge f) E slots _ (full G f) Val -- check order
  inscription : @Tune G (OEdge f) E slots _ Mark
  marks : letI : Fintype E:=slots; Dusk s Val Mark (paw κ) U scalar V m
  archive1 : letI : Fintype E:=slots; Archive G f Val 1
  archive2 : letI : Fintype E:=slots; Archive G f Val Mark
  turn t : letI : Fintype E:=slots; g t= rightSum Val Mark t/rightSum Val 1 t
attribute [instance] RangeR.slots

abbrev goal (N:Scale)(A:Hook G Empty (OEdge f))(t:ℝ):ℝ:= rightSum (startO N) A t / rightSum (G:=G) (I:=OEdge f) (startO N) 1 t
lemma arrive {N:Scale}{T V:Orders (Book G f)}{A:Hook G Empty (OEdge f)} (N':Tune A) (s':Canvas G N T A V s m)(he:Even f.val)(hr:Allowed G f (fun t u=>A t u 1)) : Nonempty (RangeR G f costO (goal N A) s m T V):=by
 refine ⟨{ E:= Empty, slots:=inferInstance, Val:= startO N, Mark := A, scalar:=1, basis:= start _ he, inscription:= N', marks:=s'.founds,archive1:= allowed_top N 1 (fun _ _ _ _=>rfl), archive2:= allowed_top N A hr,turn:=fun _=>rfl }⟩

variable {Z Z':Type}{P:ℝ} {X:Deck P Z (Book G f)}{Y:Deck P Z' (Book G c)} (D : GridStep X Y)
variable (S:StepData c f) (F:Forest S.ratio) (N: Scale)
  (κ:Horizon G f→ℝ)(μ:Horizon G c→ℝ)

-- conditional orbit-layer assembly. Uses Earth.line/per & prices of F.
abbrev FitsO := Clip (F:=nextO S F N) (V:=dropQ S F G) (paw κ) (paw μ) (firstChannel X Y).tile (lastChannel X Y).tile D.layer D.mean (fun i j=>(Step.combine X Y).deckSum (D.addon i j))
namespace RangeR
variable {κ μ F S N D} {g:ℝ →ℝ}{T V: Orders (Book G f)}
lemma along (R:RangeR G f κ g s m T V) (F:Forest S.ratio) (H:Geometry.Field.Square F)(he:Even f.val)(hc:Even c.val)(B:S.patch.Branches S.kernel G) (A:FitsO D S F N κ μ) : Nonempty (RangeR G c μ g s m (D.common T) (D.island m T V)):= by
 let W:= dropQ S F G; let Z:= nextO (G:=G) S F N; let U := fuse W R.Val Z;let M:= blade (OEdge c) W R.Mark
 have hz: Move (full G f) (full G c) W Z:= cross N S B H hc he
 refine ⟨{ E:=R.E⊕Wind F,slots:=inferInstance,Val:=U,Mark:=M,scalar:= A.recurrent T R.scalar,basis:=R.basis.integrates hz,inscription:= blade_c _ R.inscription,marks:= A.victory R.basis hz R.marks R.inscription,archive1:= continues S N B R.basis (shapeOne (G:=G) (I:=OEdge f) (E:=R.E)) R.archive1 H hc he,archive2:=continues S N B R.basis R.inscription R.archive2 H hc he,turn:=fun t=>?_ }⟩
 rw [R.turn]
 have ht := rung S N B R.basis R.inscription R.archive2 H hc he t; have hp:= rung S N B R.basis shapeOne R.archive1 H hc he t
 change _= rightSum U M t/rightSum U 1 t
 rw [show rightSum U M t = _ from ht, show rightSum U (1:Hook G _ _) t=_ from hp]; exact (mul_div_mul_right (hc:=pow_ne_zero _ (S.penaltyZ_pos (G:=G) (N.beta t/t^2)).ne') _ _).symm
end RangeR
end YM.RegulatorIR.Binding
