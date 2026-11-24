import YangMills.WilsonProof.NativeSupport.JointTicketFactorization

/-! Exact spatial separation after averaging the *shared* site-frame tags and
bond predictions on the original lattice. The Gaussian on each side is still
the one selected by those tags. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6
open Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03
open Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open Census Itinerary Greenbelt
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}

private theorem split_average {α β : Type} [Fintype α] [Fintype β] (f : α×β→ℝ) :
    likely f=likely (fun a => likely fun b => f (a,b)) := by
  unfold likely
  rw [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,mul_inv,←Finset.mul_sum]
  ring

private theorem separate_average {κ Ω ι : Type} [Fintype ι] [Fintype Ω] [Nonempty Ω]
    (g : Fintype (ι→Ω)) (V : Finset κ) (X : κ→Finset ι)
    (dis : (V:Set κ).PairwiseDisjoint X) (f : κ→(ι→Ω)→ℝ)
    (locality : ∀ i∈V,∀ v w,(∀ p∈X i,v p=w p) → f i v=f i w) :
    @likely _ g (fun u => ∏ i∈V,f i u)=∏ i∈V,@likely _ g (f i) := by
  convert! Pond.jurisdictions V X dis f locality

theorem shared_tags (K : Team R) (X : Coat T F) (H : Cash W X.x μ L Q o C T R)
    (width : X.width=o.K) (manifest : X.manifest) (k : Finset ℕ)
    (V : Finset (Molecule S)) (separate : joints T R Q.halo X.B V)
    (present : K.signs S⊆V.biUnion id)
    (J : Molecule S→Finset (Bond c)) (h : Molecule S→Bond c→ℝ→ℝ)
    (hm : ∀ p,∀ b∈J p,Measurable (h p b))
    (unit : ∀ p,∀ b∈J p,∀ t∈Set.Icc 0 (linkCap S),‖h p b t‖≤1)
    (fresh : ∀ p∈V,∀ b∈J p,zone S X.B b⊆H.unionP p) :
    (likely fun z : S.Choices =>
      let A := X.taggedL z
      ∫ v,(∏ p∈V,∏ b∈J p,h p b (lifted A R.beta b v))*
        K.into A W o.a Q.table k Q.halo (V.biUnion id) v ∂((F.order G).prod A.dice)) =
      ∏ p∈V,likely fun z : S.Choices =>
        let A := X.taggedL z
        ∫ v,raw (W:=W) (K.locate p) A k p o.a Q.table Q.halo (J p) (h p) v
          ∂((F.order G).prod A.dice) := by
  let out p (z : S.Choices) :=
    let A := X.taggedL z
    ∫ v,raw (W:=W) (K.locate p) A k p o.a Q.table Q.halo (J p) (h p) v
      ∂((F.order G).prod A.dice)
  have confined p (pv : p∈V) (z z' : S.Choices)
      (site : ∀ x∈H.unionP p,z.1 x=z'.1 x)
      (bond : ∀ b : Bond c,b.1∈H.unionP p → z.2 b=z'.2 b) : out p z=out p z' := by
    have near : Village (X.taggedL z) (X.taggedL z') (H.unionP p) :=
      ⟨rfl,rfl,rfl,fun _ _ => Iff.rfl,fun _ _ => rfl,site,bond,fun _ _ _ => rfl⟩
    exact marginal (X:=X.taggedL z) (Y:=X.taggedL z') (k:=k) (l:=k) (p:=p)
      (K.locate p) H (J p) (h p) width manifest manifest
      (hm p) (unit p) near (fresh p pv) (fun _ _ => Iff.rfl)
  trans likely fun z : S.Choices => ∏ p∈V,out p z
  · apply congrArg likely
    funext z
    exact factorization K (X.taggedL z) H width manifest k V separate present J h hm unit fresh
  let T0 p := univ.filter fun b : Bond c => b.1∈H.unionP p
  have db : (V : Set _).PairwiseDisjoint T0 := fun i hi j hj ne =>
    Finset.disjoint_left.mpr fun b hb hb' => Finset.disjoint_left.mp (separate.2 hi hj ne)
      ((mem_filter.mp hb).2) ((mem_filter.mp hb').2)
  have avgBond (s : S.SitesChoice) :
      (likely fun q : S.BondChoice => ∏ p∈V,out p (s,q)) =
      ∏ p∈V,likely fun q : S.BondChoice => out p (s,q) :=
    separate_average _ V T0 db (fun p q => out p (s,q)) (fun p pv a b eq =>
      confined p pv _ _ (fun _ _ => rfl) (fun j hj => eq j (mem_filter.mpr ⟨mem_univ _,hj⟩)))
  change (likely fun z : S.Choices => ∏ p∈V,out p z)=∏ p∈V,likely (out p)
  simp_rw [split_average (α:=S.SitesChoice) (β:=S.BondChoice)]
  simp_rw [avgBond]
  exact separate_average _ (Ω:=S.patch.FrameTag) V H.unionP separate.2 _ (fun p pv s t eq =>
    congrArg likely (funext fun b => confined p pv (s,b) (t,b) eq (fun _ _ => rfl)))

end YM.Integration.InletSusceptibility.JointTicket
