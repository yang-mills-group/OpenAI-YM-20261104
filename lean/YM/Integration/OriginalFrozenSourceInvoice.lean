import YM.Integration.OriginalIssuedMarkedRows
import YM.Integration.ActualOriginalQCharges

/-! The ultraviolet address purchase for the actual Wilson source. Each
primitive heat factor keeps its own order, and the original full path
length is charged in the same frozen token that buys the derivative frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalFrozenSourceInvoice
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato ComparisonDensity.Address LocalComparison Comparison.Density.RenderM
open RG05Readout.Native Extra.Histories
open ActualRunPacketRetuning ActualRunCalibrationTests NativeCalibrationMoodReadout QlocalOrientedTests
open ActualRunCurvaturePackets ActualRunKernelPackets NativeCurvatureTensor
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open IndependentSourcePathFamily OriginalMarkedSourceComet OriginalSourceJetAddresses
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {D : V → ℕ}

private theorem point_norm (D : ℕ) (b : Knob D) (p : Chamber) : ‖claim D b p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x; rw [one_mul]; exact registry x b p

private theorem real_part (a : Bool) (z : ℂ) : |FundedOriginalMarkedInput.component a z| ≤ ‖z‖ := by
  cases a
  · exact Complex.abs_re_le_norm z
  · exact Complex.abs_im_le_norm z

def heat (G : Gauge) (k e r : ℕ) (w : ℝ) : ℝ :=
  ∑ j : Fin (k+e+1), flour G (steep w) r j.val

private theorem heat_nn (k e r : ℕ) (w : ℝ) : 0 ≤ heat G k e r w :=
  sum_nonneg (fun _ _ => flour_nn ..)

private def rowCurrent {d : ℕ} (u : Seed G d) :=
  current (colour u.path u.color u.weight u.quadrant) (claim d u.knob u.point)

private theorem current_price {d : ℕ} (v : Seed G d) (b : Bool)
    (hb : v.quadrant = FundedOriginalMarkedInput.component b) (w : ℝ) :
    0 ≤ integerP (rowCurrent v) w ∧ integerP (rowCurrent v) w ≤
      (∑ j, ‖v.weight*NativeCurvatureTensor.coefficient v.color j‖)*Real.exp (w*∑ i, (v.path i).length) := by
  have price j : (rayOne (rowCurrent v) j).budget w = Real.exp (w*∑ i, (v.path i).length) := by
    rw [RG.Atom.budget,ray_m,one_mul]; rfl
  unfold integerP; simp_rw [price]
  refine ⟨sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _),?_⟩
  rw [sum_mul]
  apply sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  change ‖(v.quadrant (v.weight*NativeCurvatureTensor.coefficient v.color j)) • claim d v.knob v.point‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,hb]
  calc
    _ ≤ |FundedOriginalMarkedInput.component b (v.weight*NativeCurvatureTensor.coefficient v.color j)| * 1 :=
      mul_le_mul_of_nonneg_left (point_norm _ _ _) (abs_nonneg _)
    _ ≤ _ := (mul_one _).le.trans (real_part _ _)

omit [Fintype V] [DecidableEq V] in
theorem single {I : V → Type} [∀ v, Fintype (I v)] (X : ∀ t, I t → Seed G (D t))
    (k : V → ℕ) (e : ℕ) (w : ℝ) (i : V) (a : I i) (b : Bool)
    (hb : (X i a).quadrant = FundedOriginalMarkedInput.component b) :
    let u := X i a
    charge X k e w i a ≤ (∑ j, ‖u.weight*NativeCurvatureTensor.coefficient u.color j‖)*
      Real.exp (w*∑ t, (u.path t).length) * heat G (k i) e u.rank w := by
  intro u
  have h := current_price u b hb w
  calc
    _ = integerP (rowCurrent u) w * heat G (k i) e u.rank w := by
      change (∑ j : Fin (k i+e+1), |integerP (rowCurrent u) w*flour G (steep w) u.rank j.val|) = _
      simp_rw [abs_of_nonneg (mul_nonneg h.1 (flour_nn ..))]
      exact (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h.2 (heat_nn ..)

section physical
variable {R : Run G} {p L n : ℕ} {hn : n ≤ L} {B : MS.Local.Physical.Deck G}
  (Q : MS.Land.Prescription B) (datum : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders k : V → ℕ) (N e : ℕ) (w : ℝ)
  (normal : V → ℂ) (quad : V → Bool)

private abbrev Row := ActualOriginalQPackets.Row (R:=R) u
private abbrev Fibre (i : V) := {s : Row (R:=R) u // s.1.1 = i}

/-- Each colour and derivative is bought by the old physical frozen token,
including its exact stored signed Laurent correction. -/
theorem perRow (hL : L ≤ N) (i : V) (t : Fibre (R:=R) u i) :
    let X := FundedOriginalMarkedInput.chosen Q datum u μ orders normal quad
    let T := ActualOriginalQPackets.token Q datum u μ orders N t.val
    let z := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) t.val:ℤ))
    let s := (datum.choice i).2.1
    (∑ a : Word (depth s), charge X k e w i (t,a)) ≤
      (frameRate (depth s) s.2*(scaleToken z T).coin)*
        (‖normal i‖*Real.exp (w*T.fall)*heat G (k i) e (tokenRank R (ActualOriginalQPackets.degree u) t.val) w) := by
  rcases t with ⟨t,rfl⟩
  intro X T z s
  let H := heat G (k t.1.1) e (tokenRank R (ActualOriginalQPackets.degree u) t) w
  let f (j) (a : Word (depth s)) := ‖bareColor u t j * (ActualOriginalQReaders.fee Q u μ orders t.1 *
    Motion.scalar (datum.motion t.1.1) (ActualRunQlocalNativeTuple.constant datum t.1.1*
      multiplier s ((R.family.S.toDepth hn p).count.val:ℝ)⁻¹ a))‖
  have hs := frozen_purchased Q datum u μ orders N hL t
  let t' : Fibre (R:=R) u t.1.1 := ⟨t,rfl⟩
  have bills a : charge X k e w t.1.1 (t',a) ≤
      (∑ j,f j a)*(‖normal t.1.1‖*Real.exp (w*T.fall)*H) := by
    have one := single X k e w t.1.1 (t',a) (quad t.1.1) rfl
    refine one.trans_eq ?_
    have weight j : ‖(X t.1.1 (t',a)).weight*NativeCurvatureTensor.coefficient (X t.1.1 (t',a)).color j‖ =
        ‖normal t.1.1‖*f j a := by
      dsimp only [f]; rw [← norm_mul]
      congr 1; dsimp [X,FundedOriginalMarkedInput.chosen,bareColor,t',s]; ac_rfl
    simp_rw [weight,←Finset.mul_sum]
    change (‖normal t.1.1‖*(∑ j,f j a))*Real.exp (w*T.fall)*H = _
    ring
  calc
    _ ≤ ∑ a : Word (depth s), (∑ j,f j a)*(‖normal t.1.1‖*Real.exp (w*T.fall)*H) :=
      sum_le_sum fun a _ => bills a
    _ = (∑ j,∑ a,f j a)*(‖normal t.1.1‖*Real.exp (w*T.fall)*H) := by rw [←sum_mul,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) (heat_nn ..))

/-- A numerical row tariff on the actual pre-existing mark. It is fixed
before the period's external tests and never uses a negative g power. -/
def weight (i : V) : ℝ :=
  1 + ∑ t : Fibre (R:=R) u i, ‖normal i‖ * |frameRate (depth (datum.choice i).2.1) (datum.choice i).2.1.2| *
    heat G (k i) e (tokenRank R (ActualOriginalQPackets.degree u) t.val) w

theorem input (hL : L ≤ N) :
    bill (FundedOriginalMarkedInput.chosen Q datum u μ orders normal quad) k e w ≤
      ActualOriginalQPackets.packetCost Q datum u μ orders N (weight datum u k e w normal) w := by
  let X := FundedOriginalMarkedInput.chosen Q datum u μ orders normal quad
  let W := weight datum u k e w normal
  let f (s : Row (R:=R) u) := ‖ActualOriginalQReaders.fee Q u μ orders s.1‖*
    ActualOriginalQCharges.rowPrice datum u W w s
  have each (i) (t : Fibre (R:=R) u i) :
      (∑ b : Word (depth (datum.choice i).2.1), charge X k e w i (t,b)) ≤ f t.val := by
    let s := (datum.choice i).2.1
    let H := heat G (k i) e (tokenRank R (ActualOriginalQPackets.degree u) t.val) w
    let T := ActualOriginalQPackets.token Q datum u μ orders N t.val
    let z := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ)^(-(fieldRank R (ActualOriginalQPackets.degree u) t.val:ℤ))
    let C := (scaleToken z T).coin*Real.exp (w*T.fall)
    have expand (W' : V → ℝ) : W' i*C = ‖ActualOriginalQReaders.fee Q u μ orders t.val.1‖*
        ActualOriginalQCharges.rowPrice datum u W' w t.val := by
      simpa only [Poly.solo_toll,t.property,C,scaleToken,mul_assoc] using
        ActualOriginalQCharges.token_charge datum u Q μ orders N hL W' w t.val
    have positive : 0 ≤ C := by
      rw [←one_mul C,expand (fun _ => 1)]
      exact mul_nonneg (norm_nonneg _) (ActualOriginalQCharges.row_price_nonneg datum u _ w (fun _ => zero_lt_one) _)
    have coeff : ‖normal i‖ * frameRate (depth s) s.2 * H ≤ W i := by
      have node := Finset.single_le_sum (s:=univ) (f:=fun b : Fibre (R:=R) u i =>
        ‖normal i‖*|frameRate (depth s) s.2| * heat G (k i) e (tokenRank R (ActualOriginalQPackets.degree u) b.val) w)
        (fun b _ => mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (heat_nn ..)) (mem_univ t)
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _))
        (heat_nn ..)).trans (node.trans (le_add_of_nonneg_left zero_le_one))
    calc
      _ ≤ (frameRate (depth s) s.2*(scaleToken z T).coin)*(‖normal i‖*Real.exp (w*T.fall)*H) :=
        perRow Q datum u μ orders k N e w normal quad hL i t
      _ = (‖normal i‖*frameRate (depth s) s.2*H)*C := by dsimp [C]; ring
      _ ≤ W i*C := mul_le_mul_of_nonneg_right coeff positive
      _ = _ := expand W
  let E : ((i : V) × Fibre (R:=R) u i) ≃ Row (R:=R) u :=
    {toFun := fun a => a.2.val,invFun := fun s => ⟨s.1.1,⟨s,rfl⟩⟩,
     left_inv := by rintro ⟨i,t,h⟩; subst i; rfl,right_inv := fun _ => rfl}
  rw [ActualOriginalQCharges.packet_cost datum u Q μ orders N hL]
  calc
    _ = ∑ i, ∑ t : Fibre (R:=R) u i, ∑ b : Word (depth (datum.choice i).2.1), charge X k e w i (t,b) := by
      unfold bill; simp_rw [Fintype.sum_prod_type]; rfl
    _ ≤ ∑ i, ∑ t : Fibre (R:=R) u i, f t.val := sum_le_sum fun i _ => sum_le_sum fun t _ => each i t
    _ = ∑ t : ((i : V) × Fibre (R:=R) u i), f (E t) :=
      (Fintype.sum_sigma (fun t : ((i : V) × Fibre (R:=R) u i) => f (E t))).symm
    _ = ∑ s : Row (R:=R) u, f s := E.sum_comp f

end physical
end YM.Integration.OriginalFrozenSourceInvoice
end
