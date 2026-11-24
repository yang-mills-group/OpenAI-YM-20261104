import YangMills.WilsonProof.NativeSupport.JointTicketMarginal

/-! Separation of the measured ticket inside the original correlated Gaussian
and Haar sector integral, prior to averaging the shared blocking choices. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6
open Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03
open Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat Census Itinerary
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

theorem factorization (K : Team R) (X : Coat T F) (H : Cash W X.x μ L Q o C T R)
    (width : X.width=o.K) (manifest : X.manifest) (k : Finset ℕ)
    (V : Finset (Molecule S)) (separate : joints T R Q.halo X.B V)
    (present : K.signs S⊆V.biUnion id)
    (J : Molecule S→Finset (Bond c)) (h : Molecule S→Bond c→ℝ→ℝ)
    (hm : ∀ p,∀ b∈J p,Measurable (h p b))
    (unit : ∀ p,∀ b∈J p,∀ t∈Set.Icc 0 (linkCap S),‖h p b t‖≤1)
    (fresh : ∀ p∈V,∀ b∈J p,zone S X.B b⊆H.unionP p) :
    let D := (F.order G).prod X.dice
    let field := K.into X W o.a Q.table k Q.halo (V.biUnion id)
    (∫ v,(∏ p∈V,∏ b∈J p,h p b (lifted X R.beta b v))*field v ∂D) =
      ∏ p∈V,∫ v,raw (W:=W) (K.locate p) X k p o.a Q.table Q.halo (J p) (h p) v ∂D := by
  intro D field
  let g p := raw (W:=W) (K.locate p) X k p o.a Q.table Q.halo (J p) (h p)
  have split (v : F.Slice G × Air f G) :
      (∏ p∈V,∏ b∈J p,h p b (lifted X R.beta b v))*field v=∏ p∈V,g p v := by
    rw [show field v=∏ p∈V,(K.locate p).into X W o.a Q.table k Q.halo p v from
      K.sticksU (X.wrapY v.1) k (unweave separate) present v.2,← prod_mul_distrib]
    rfl
  have meas p : Measurable (g p) := measurable_raw (K.locate p) H (J p) (h p) width (hm p)
  have integ p : Integrable (g p) D :=
    (raw_price (K.locate p) X H width manifest k p (J p) (h p) (hm p) (unit p)).1
  have integrable_all : Integrable (fun v => ∏ p∈V,g p v) D := by
    apply (K.tip X k H width manifest (V.biUnion id)).2.1.norm.mono'
      (Finset.measurable_fun_prod V (fun p _ => meas p)).aestronglyMeasurable
    apply ae_of_all D
    intro v
    rw [←split,norm_mul,norm_prod]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply prod_le_one (fun p _ => norm_nonneg _)
    intro p _
    rw [norm_prod]
    exact prod_le_one (fun _ _ => norm_nonneg _) fun b bJ => unit p b bJ _ (in_band X _ b v)
  let ga p (a : F.Slice G) := ∫ v,g p (a,v) ∂X.dice
  let I p := podium S G (H.unionP p) X.B
  have dis : (V : Set _).PairwiseDisjoint H.unionP := separate.2
  have pos := (H.laws.data.localP F X rfl width manifest).sails.fullC
  have unchanged (p) (pV : p∈V) (a b : F.Slice G) (fs : ∀ i:F.Free,
      atEdge S i.val∈H.unionP p → a i=b i) (u v) (same : swim (I p) u=swim (I p) v) :
      g p (a,u)=g p (b,v) :=
    concur (K.locate p) H (J p) (h p)
      ⟨(Village.refl _ _).wrap _ _ fs,(observe _).mp same,fun _ _ => Iff.rfl⟩
      (Finset.Subset.refl _) (fresh p pV)
  have gaussian (z : F.Slice G) :
      (∫ v,∏ p∈V,g p (z,v) ∂X.dice)=∏ p∈V,ga p z := by
    apply Pond.island pos.posSemidef V I
    · intro i hi j hj hn a ha b hb
      apply X.shutter.width X.plate
      by_contra outside
      have distance := le_of_not_gt outside
      have large : 100≤X.B := H.laws.data.room.sight.1
      exact Finset.disjoint_left.mp (dis hi hj hn)
        ((mem_filter.mp ha).2 (along S b) (distance.trans (by omega)))
        ((mem_filter.mp hb).2 (along S b) (by rw [separation_self]; omega))
    · exact fun p _ => (meas p).comp (measurable_const.prodMk measurable_id)
    · exact fun p pV u v => unchanged p pV z z (fun _ _ => rfl) u v
  let A p := univ.filter fun i : F.Free => atEdge S i.val∈H.unionP p
  have haar := Pond.marched (fun _ : F.Free => G.probHaar) V A
    (fun i hi j hj ne => Finset.disjoint_left.mpr fun a ha hb =>
      Finset.disjoint_left.mp (dis hi hj ne) ((mem_filter.mp ha).2) ((mem_filter.mp hb).2))
    ga (fun p _ => ((meas p).stronglyMeasurable.integral_prod_right').measurable)
    (fun p pV a b eq => integral_congr_ae (ae_of_all _ fun v =>
      unchanged p pV a b (fun i hi => eq i (mem_filter.mpr ⟨mem_univ _,hi⟩)) v v rfl))
  simp_rw [split]
  rw [integral_prod _ integrable_all]
  simp_rw [gaussian]
  change (∫ a,∏ p∈V,ga p a ∂F.order G)=_
  rw [show (∫ a,∏ p∈V,ga p a ∂F.order G)=∏ p∈V,∫ a,ga p a ∂F.order G from haar]
  exact prod_congr rfl fun p _ => (integral_prod (g p) (integ p)).symm

end YM.Integration.InletSusceptibility.JointTicket
