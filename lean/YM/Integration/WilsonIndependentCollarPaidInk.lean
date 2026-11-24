import YM.Integration.WilsonIndependentCollarInkPrice

/-! The actual output of the elected marked-path compiler summed over its
own stencil measures, all path atoms and all relative placements. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPaidInk
open Filter Function Finset Lattice RG Wilson Precision PhysicalNext.Repeat.Legato Exterior Work.F08 MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonIndependentCollarPrintIncome WilsonIndependentCollarRootedWidth
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [DecidableEq ι] {D:ι→ℕ}

def Income (I:Gear G)(w:Widths G)(p k:ℕ)(S:Finset ι)(v:ι)(Y:Outerm G D)(C:ℝ):Prop:=
  let out:=issue w p k I
  let t:=rooted S.card out.strip
  ∀(o:Cover)(j:ℕ)(_hj:j<p)(r:Fin (k+j+1)),
    let B:=packetH S (fun y=>Y y S) k p v o
    let Z:=fun c:Frill S v=>B c j r
    ∃X:(u:Frill S v × RadP G r.val)→Stationary.Ink G r.val→Measure (Sky D),
      (∀u,Barn (Z u.1 u.2) (X u)) ∧ SumBudget
        (fun x:Frill S v × RadP G r.val=>
          Real.exp (t*feeH (toe S v o x.1) v S)*lease (Z x.1 x.2) (X x) t) C

theorem dated {e:ℕ}(V:Realm G (e+1) Credit.leanC)(w:Widths G)(m:ℕ)(hm:V.anchor ≤ m)
    (k:ι→ℕ)(S:Finset ι)(v:ι)(front:v∈S)(Y:Outerm G D)
    (auth:∀y,Auth (mass k S) (Y y S))(P:Credit)(A Z:ℝ)(non:0≤A)(hZ:1≤Z)(yr:V.y m≤Z)
    (uniform:Uniform V Y m hm (P.buy Z*A)):
    let U:=V.mint m hm
    let out:=issue w (e+1) (mass k S) U.gear
    let t:=rooted S.card out.strip
    U.gear.s=2*U.σ → U.σ≤1 → out.fee≤V.y m → out.strip⁻¹≤V.y m →
    0<t ∧ t⁻¹≤(S.card+1)*V.y m ∧
      Income U.gear w (e+1) (mass k S) S v Y
        ((WilsonIndependentCollarInkPrice.cost G P (mass k S) (e+1) S.card (Fintype.card (S.erase v))).buy Z*A^S.card):=by
  intro U out t twice upper charge rent
  have span:out.strip≤U.σ:=by
    apply out.narrow.trans
    apply (min_le_right ..).trans
    apply (min_le_left ..).trans
    rw [twice];linarith [U.width]
  have slope:U.σ⁻¹≤Z:=((inv_le_inv₀ U.width out.openStrip).2 span).trans (rent.trans yr)
  have sprout:=WilsonIndependentCollarRootedWidth.original w U.gear U.σ U.width twice (e+1) (mass k S) S.card
  refine ⟨sprout.1,sprout.2.2.2.trans (mul_le_mul_of_nonneg_left rent (by positivity)),?_⟩
  intro o j hj r B z
  have fund (y)(i:ℕ)(hi:i<e+1)(r):=uniform y S i (show i≤e by omega) r
  have given:=WilsonIndependentCollarRootedInk.original U.gear U.σ U.width twice w
    (mass k S) (e+1) (e+1) le_rfl S v front (fun y=>Y y S) auth ((P.buy Z*A)^S.card)
    (pow_nonneg (mul_nonneg (zero_le_one.trans (P.purchase hZ)) non) _) fund o j hj r
  obtain ⟨X,issued,price⟩:=given
  exact ⟨X,issued,price.1,price.2.1,price.2.2.trans (WilsonIndependentCollarInkPrice.original P (mass k S) (e+1) S v front
    U.width upper hZ slope (zero_le_one.trans out.funded) (charge.trans yr) non)⟩

end YM.Integration.WilsonIndependentCollarPaidInk
end
