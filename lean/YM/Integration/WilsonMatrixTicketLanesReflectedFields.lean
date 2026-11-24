import YM.RGComparison.Core16.Silk.Kite
import YM.Integration.WilsonMatrixTicketLanesRegulatorPrincipal

/-! Connected coefficients of two complete original compact fields at their actual translated stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedFields
open Function Filter Finset Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open RGComparison.Core16.Spool RGComparison.Core16.Silk
open scoped Topology Classical
variable {G : Gauge}

private theorem joint {A D H I J : Type} [Fintype H] {X : Shelf G A D}
    {p : Stuff G H I} {q : Stuff G H J} {ψ : (I→G.Color)→ℝ} {φ : (J→G.Color)→ℝ}
    {f h : Melody G H} {n m : ℕ} {C E : ℝ} (ha : Visible X ψ f p n C) (hb : Visible X φ h q m E)
    (cpos : 0≤C) : Visible X (unite ψ φ) (fun g x=>f g x*h g x) (woven p q) (n+m) (C*E) := by
  obtain ⟨V,hV,vc,onV⟩:=ha.stamp
  obtain ⟨W,hW,wc,onW⟩:=hb.stamp
  refine ⟨fun g good=>(ha.env g good).mul (hb.env g good),?_,V∪W,(Finset.card_union_le ..).trans (Nat.add_le_add hV hW),
    Silk.coveredBy p q vc wc,?_⟩
  · intro g good x
    rw [abs_mul]; exact mul_le_mul (ha.price g good x) (hb.price g good x) (abs_nonneg _) cpos
  intro g good gp x clear
  rw [onV g good gp x (fun i hi=>clear i (mem_union_left _ hi)),onW g good gp x (fun i hi=>clear i (mem_union_right _ hi))]
  rfl

variable {c f : Side} (S : StepData c f) (T : Forest S.ratio)
    {I J : Type} [Fintype I] [Fintype J] (A : I→Lamp G) (B : J→Lamp G)
    (x : I→Site f) (y : J→Site f) (a b : Bool) {P : Oven S.patch} (X : P.Form G) (u : Directions G c)
local notation "O" => Spool.lens (S:=S) u X T

def series : Roll := Silk.joining O (earns S T A x) (earns S T B y) (look a ∘ sight A) (look b ∘ sight B)

/-- Both means and the joint product are taken in the authentic single positive normalized Wilson conditional. -/
def covariance (g : ℝ) := (O).expect g (fun z=>echo S T A x a g z*echo S T B y b g z)-
    (O).expect g (echo S T A x a g) * (O).expect g (echo S T B y b g)

/-- The priced coefficient series belongs to that specific compact conditional. -/
theorem measured (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S) (pin : ∀i,‖u i‖≤X.Q) :
    train (covariance S T A B x y a b X u) (series S T A B x y a b X u) := by
  have steady : (O).Steady := Oven.paints T offer pin large
  obtain ⟨C,hC,ac⟩ := encouraging A
  obtain ⟨E,_,bc⟩ := encouraging B
  have va := Spool.offers S T A x offer.good a (ac a)
  have vb := Spool.offers S T B y offer.good b (bc b)
  have combined := Silk.booked O steady (joint va vb hC) ((Silk.mixed_hot (sphere A a) (sphere B b)).of_le le_top)
  exact combined.deduct ((Silk.booked O steady va ((sphere A a).of_le le_top)).produces
    (Silk.booked O steady vb ((sphere B b).of_le le_top)))

private def support (K : I→Lamp G) (o : I→Site f) : Finset T.Free :=
  univ.filter fun e=>∃j : Slice K, legs K o j=e.1

omit [Fintype J] in
private theorem covers (good : Good X) : celery (earns S T A x) (support S T A x) X.Q := by
  intro j
  unfold earns; split_ifs
  · change ‖(0:G.Color)‖≤X.Q; simpa using good.thick.1.le
  · exact mem_filter.mpr ⟨mem_univ _,⟨j,rfl⟩⟩

/-- The input to the original spatial price is the actual fine coordinate of each placed stencil leg. -/
theorem price (offer : P.Offers X S.kernel) (large : Bid.Larger (G:=G) S) (pin : ∀i,‖u i‖≤X.Q)
    {C : ℝ} {n j e : ℕ} (hC : 0≤C) (prices : Past X C n n n) (degree : j≤n)
    (distance : ∀i : Slice A,∀k : Slice B,e≤Lattice.separation (legs A x i).1 (legs B y k).1) :
    |nth j (series S T A B x y a b X u)| ≤ C/costLamp X e*bond_fee (look a ∘ sight A) (look b ∘ sight B) X.Q n := by
  have steady : (O).Steady := Oven.paints T offer pin large
  apply Silk.ramp steady (covers S T A x X offer.good) (covers S T B y X offer.good)
    (sphere A a) (sphere B b) hC prices _ degree
  intro i hi k hk
  obtain ⟨s,hs⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨v,hv⟩ := (Finset.mem_filter.mp hk).2
  change e ≤ Lattice.separation i.1.1 k.1.1
  rw [←hs,←hv]; exact distance s v

end YM.Integration.WilsonMatrixTicketLanesReflectedFields
