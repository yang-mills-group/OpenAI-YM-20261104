import YM.Integration.WilsonCapturedWindingCharge
import YM.Trace.Physicalv2.GermChain

/-! Subtract the actual measured terminal counterterm from the original
signed sources. The stable crossing gets a zero measured endpoint and
needs no estimate of the ultraviolet canonical label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedSignedCrossing
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 YM.MergeProof
open MeasureTheory Germ
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d : ℕ)

private theorem materials (hG : G.Simple) : Ribbons.Materials R.family := by
  have old := R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  obtain ⟨_,tabs,fees,_,_,_,_⟩ := old
  exact ⟨hG,R.makes,⟨R.family.path,R.t,R.stories,rfl⟩,tabs,_,R.doors,_,_,_,fees,(R.again hG).1.scrim⟩

private theorem neg_cal {N p i : ℕ} (h : Opened R.family d i p) (hN : i≤N) (x : R.family.label d) :
    calValues (C:=R.family) d N p i (-x) = -(calValues (C:=R.family) d N p i x) := by
  have zero := negative_cal (d:=d) (N:=N) (p:=p) (i:=i) R.makes h hN x
  exact eq_neg_of_add_eq_zero_left zero

theorem purchased (hG : G.Simple) {γ ε : ℝ} (hγ : 0<γ) (hγ' : γ<rate)
    (he : 0<ε) (he' : ε≤1) :
    ∀ᶠ t : ℕ in atTop, ∀ p N, t≤N → ∀ (qt : store R.family d p t) {rt : ℝ},
      reads (C:=R.family) d N p t qt rt →
      ∃ x : R.family.label d, page (C:=R.family) d p t ((R.family.factory d N p).entries t x) =
          page (C:=R.family) d p t qt ∧
      ∀ {b : ℕ} (_ : t≤b) (_ : b≤N) (qb : store R.family d p b)
        {rb D : ℝ} (_ : reads (C:=R.family) d N p b qb rb)
        (_ : (R.family.labels.level d).coeffSize qb.x ≤ rb) (_ : 0≤D)
        {err f : Er R.family p},
        err t = value (C:=R.family) d N p t qt - calValues (C:=R.family) d N p t x →
        err b = value (C:=R.family) d N p b qb - calValues (C:=R.family) d N p b x →
        (∀ i≥t, i<b → Foreground R.family d N p i (f i) D ∧
          err i = transition (C:=R.family) d N p i (err (i+1)) + f i) →
        let B := (1+4*stock R.family b)*rb
        ∃ (Q : ∀ i, store R.family d p i) (y : ℕ→R.family.label d), ∀ i≥t, i≤b →
          Shot R.family d N p err i (Q i) (y i) (hike R.family b i rate*B+2*D) ∧
          mCost R.family d N p i (y i) ≤
            hike R.family t i γ*(2*((i:ℝ)-t)*D) + 2*ε*hike R.family b i rate*B := by
  obtain ⟨a,openA⟩ := eventually_atTop.1 (open_late R.family hG d)
  filter_upwards [eventually_ge_atTop a,WilsonCapturedSignedRemainder.purchased R d hG,
    crossing R.family d (materials R hG) hγ hγ' he he'] with t late split move
  intro p N tN qt rt receipt
  obtain ⟨s,x,zero,fit,paid,field,_⟩ := split p N tN qt receipt
  refine ⟨x,fit,?_⟩
  intro b tb bN qb rb D bb head pos err f low high steps
  have anchor : Anchored R.family d N p t err 0 := by
    refine ⟨s,_,paid,?_,Filter.Eventually.of_forall (congrFun (low.trans field))⟩
    rw [zero]
    simp [Frame.coeffSize]
  have hb := openA b (late.trans tb) p
  obtain ⟨v,z,bill,empty,realized,_,_⟩ := fresh_split (C:=R.family) (d:=d) (N:=N) (p:=p) (i:=b) R.makes hb bN qb bb head
  change R.family.label d at z
  let cal := calValues (C:=R.family) d N p b
  have delta : cal (z-x) = cal z - cal x := by
    calc
      _ = cal (z + -x) := congrArg cal (sub_eq_add_neg z x)
      _ = cal z + cal (-x) := cal_add (C:=R.family) d N p b R.makes hb.post bN z (-x)
      _ = cal z - cal x := congrArg (cal z + ·) (neg_cal R d hb bN x)
  have registered : Shot R.family d N p err b v (z-x) ((1+4*stock R.family b)*rb) := by
    refine ⟨bill,empty,?_⟩
    calc
      err b = value (C:=R.family) d N p b qb - calValues (C:=R.family) d N p b x := high
      _ = (value (C:=R.family) d N p b v + calValues (C:=R.family) d N p b z) - calValues (C:=R.family) d N p b x :=
        congrArg (fun a => a - calValues (C:=R.family) d N p b x) realized
      _ = value (C:=R.family) d N p b v + calValues (C:=R.family) d N p b (z-x) := by
        exact (show (value (C:=R.family) d N p b v + cal z) - cal x =
          value (C:=R.family) d N p b v + (cal z - cal x) from by abel).trans
          (congrArg (value (C:=R.family) d N p b v + ·) delta.symm)
  obtain ⟨Q,y,works⟩ := move p N tb bN pos steps anchor ⟨v,z-x,registered⟩
  exact ⟨Q,y,fun i ti ib => by simpa only [zero_add] using works i ti ib⟩

end YM.Integration.WilsonCapturedSignedCrossing
