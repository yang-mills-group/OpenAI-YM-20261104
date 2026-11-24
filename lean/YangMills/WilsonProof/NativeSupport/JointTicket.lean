import YangMills.WilsonProof.NativeSupport.JointCoatEnergy
import YM.MergeProof.Wreath

/-! The actual mixed ticket with a bounded real function of each selected
transition energy. Measurements stay inside every native integration.
For a complex activity the two real parts can be separate priced tickets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
open Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum
open Sector Footprint Packets SliceRows Control Window Pulse Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Merge Merge.Palette JointCoat
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {ι : Type} {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G}
    {T : Tube G S} {F : Forest S.ratio} {R : Rep G f} {W μ x C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

def raw (K : Team R) (X : Coat T F) (k : Finset ℕ) (p : Molecule S)
    (a : ℝ) (A : ChartRatio G) (l : ℕ) (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ) :=
  fun v => (∏ b∈J,h b (lifted X R.beta b v))*K.into X W a A k l p v

theorem raw_price (K : Team R) (X : Coat T F) (Y : Cash W X.x μ L Q o C T R)
    (width : X.width=o.K) (manifest : X.manifest) (k : Finset ℕ) (p : Molecule S)
    (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ) (hm : ∀ b∈J,Measurable (h b))
    (unit : ∀ b∈J,∀ t∈Set.Icc 0 (linkCap S),‖h b t‖≤1) :
    let D := (F.order G).prod X.dice
    let f := raw (W:=W) K X k p o.a Q.table Q.halo J h
    Integrable f D ∧ (∫ v,‖f v‖ ∂D) ≤
      if K.signs S⊆p then K.weight*∏ i∈p\K.signs S,Y.text i else 0 := by
  intro D integrand
  let body := K.into X W o.a Q.table k Q.halo p
  have ticket := K.tip X k Y width manifest p
  have bound (v : F.Slice G × Air f G) : ‖integrand v‖≤‖body v‖ := by
    change ‖(∏ b∈J,h b (lifted X R.beta b v))*body v‖≤_
    rw [norm_mul,norm_prod]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun b bJ =>
      unit b bJ _ (in_band X _ b v)
  have mh := Finset.measurable_fun_prod J fun b bJ =>
    (hm b bJ).comp (measurable_lifted X Y width b)
  have mg : Measurable integrand := mh.mul ticket.1.1
  refine ⟨ticket.2.1.norm.mono' mg.aestronglyMeasurable (ae_of_all D bound),?_⟩
  exact (integral_mono_of_nonneg (ae_of_all D (fun v => norm_nonneg (integrand v)))
    ticket.2.1.norm (ae_of_all D bound)).trans ticket.2.2

variable (M : ι→Leaf R) (Y : Cash W x μ L Q o C T R) (χ : Chi)
local notation "tickets" => Tickets (sign M S)

def act (U : Config G c) (p : Molecule S) (i : tickets) (J : Finset (Bond c))
    (h : Bond c→ℝ→ℝ) : ℝ :=
  let _ := Y
  likely fun r : Greenbelt.Reserve S =>
    let V := prism T x χ o.K U (allot r)
    if standsIn V R Q.halo p then likely fun j : S.Choices =>
      let X := (planted V p).taggedL j
      ∫ v,raw (W:=W) (team M i) X (own p) p o.a Q.table Q.halo J h v
        ∂(((allot r).order G).prod X.dice)
    else 0

theorem no_new (U : Config G c) (p : Molecule S) (i : tickets) (h : Bond c→ℝ→ℝ) :
    act M Y χ U p i ∅ h = Palette.act M Y χ U p i := by
  unfold act Palette.act Team.lotus Team.bloom Team.steep Team.tithe raw
  simp only [prod_empty,one_mul]

theorem price (U : Config G c) (p : Molecule S) (i : tickets) (J : Finset (Bond c))
    (h : Bond c→ℝ→ℝ) (hm : ∀ b∈J,Measurable (h b))
    (unit : ∀ b∈J,∀ t∈Set.Icc 0 (linkCap S),‖h b t‖≤1) :
    ‖act M Y χ U p i J h‖ ≤
      if i.reach⊆p then (∏ j∈i.val,(M j).weight)*∏ j∈p\i.reach,Y.text j else 0 := by
  letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  unfold act
  apply Palette.likely_norm
  intro r
  dsimp only
  split
  · apply Palette.likely_norm
    intro j
    let V := prism T x χ o.K U (allot r)
    let X := (planted V p).taggedL j
    have ht := raw_price (team M i) X Y rfl (planted_valid V p) (own p) p J h hm unit
    exact (norm_integral_le_integral_norm _).trans (ht.2.trans_eq (by
      rw [Palette.label,Palette.worth]; congr!))
  · rw [norm_zero]
    split
    · exact mul_nonneg (prod_nonneg fun j _ => (M j).profit)
        (prod_nonneg fun j _ => Y.positive j)
    · rfl

end YM.Integration.InletSusceptibility.JointTicket
