import YangMills.WilsonProof.NativeSupport.JointTicketMarginal

/-! The original measurements agree between different block forests whenever their
parent choices agree on the charged coarse support. The change of forest uses the
native common Haar reservoir and the exact marginal of each full Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Art Rotation Horticulture ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {F F' : Forest S.ratio}
    {T : Tube G S} {P : Teller G} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
    {X : Coat T F} {Y : Coat T F'} {Z : Support c} {u v : Air f G} {k k' : Finset ℕ}

theorem forest_energy (A : Clump X Y Z u v k k' R) (room : Room P S T X.x)
    (b : Bond c) (inside : zone S X.B b ⊆ Z) :
    energy X (X.liftA R.beta u) b=energy Y (Y.liftA R.beta v) b := by
  have reach : predReach S.patch≤X.B := by
    change predReach S.patch≤radiusB X.x
    have paid := room.frame
    omega
  have large : 100≤X.B := room.sight.1
  have has (j : Site c) (near : separation b.1 j≤26*X.B) : j∈Z :=
    inside (halo_spec.mpr ⟨b.1,mem_singleton_self _,near⟩)
  have left : b.1∈Z := has _ (by rw [separation_self]; omega)
  have right : b.1+step b.2∈Z := has _ ((sep_step _ _).trans (by omega))
  have agree : AgreeNear S.ratio.parent b.1 (predReach S.patch)
      (X.input (X.liftA R.beta u)) (Y.input (Y.liftA R.beta v)) := by
    intro i hi
    apply A.quarters room
    intro j hj
    apply has j
    exact (separation_triangle b.1 (atEdge S i) j).trans (by
      change separation b.1 (atEdge S i)≤predReach S.patch at hi
      omega)
  have pred := prediction_near_eq (funds_branch room.accepted) _ _ X.k b agree
  have tag (U : Config G f) : S.prediction U X.k b=S.prediction U Y.k b := by
    have same : S.connector U X.k.1 b=S.connector U Y.k.1 b := by
      funext j
      simp only [StepData.connector,StepData.frames,A.site _ left,A.site _ right]
    simp only [StepData.prediction,same,A.bond _ left]
  unfold JointCoat.energy
  rw [A.actual b left right,pred,tag]

theorem forest_marginal (M : Team R) (X : Coat T F) (X' : Coat T F') (s : Molecule S)
    (hK : X.width=o.K) (hK' : X'.width=o.K) (hy : X'.x=X.x)
    (hv : X.V=X'.V) (hc : X.χ=X'.χ) (H : Cash W X.x μ L Q o C T R)
    (hw : ∀ i : Site f,S.ratio.parent i∈H.unionP s → F.up i=F'.up i)
    (ho : X.seeds=X'.seeds) (hk : X.k=X'.k) (hm : X.manifest) (hm' : X'.manifest)
    (l : Finset ℕ) (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ)
    (mh : ∀ b∈J,Measurable (h b)) (unit : ∀ b∈J,∀ t∈Set.Icc 0 (linkCap S),‖h b t‖≤1)
    (fresh : ∀ b∈J,zone S X.B b⊆H.unionP s) :
    (∫ v,raw (W:=W) M X l s o.a Q.table Q.halo J h v ∂((F.order G).prod X.dice)) =
      ∫ v,raw (W:=W) M X' l s o.a Q.table Q.halo J h v ∂((F'.order G).prod X'.dice) := by
  have hM {F0 : Forest S.ratio} (Z : Coat T F0) (hx : Z.x=X.x) (ht : Z.width=o.K) :
      Measurable (raw (W:=W) M Z l s o.a Q.table Q.halo J h) :=
    measurable_raw M (show Cash W Z.x μ L Q o C T R from hx.symm ▸ H) J h ht mh
  rw [integral_prod _ (raw_price M X H hK hm l s J h mh unit).1,integral_prod _
    (raw_price M X' (show Cash W X'.x μ L Q o C T R from hy.symm ▸ H) hK' hm' l s J h mh unit).1]
  rw [← Pond.reception (Horticulture.reserve (S:=S) G F) _ ((hM X rfl hK).stronglyMeasurable.integral_prod_right' (ν:=X.dice)).measurable,
    ← Pond.reception (Horticulture.reserve (S:=S) G F') _ ((hM X' hy hK').stronglyMeasurable.integral_prod_right' (ν:=X'.dice)).measurable]
  apply integral_congr_ae; filter_upwards with u
  let I:= podium S G (H.unionP s) X.B; let Xa:= X.wrapY (bridge (S:=S) F u); let Yf:=X'.wrapY (bridge (S:=S) F' u)
  have he: Crop Xa Yf (H.unionP s) := ⟨hy.symm,hK.trans hK'.symm,hc,fun _ _=> ho ▸ Iff.rfl, foreclose hw u,
    fun i _=> (congr_fun (congr_arg Prod.fst hk) i), fun i _=> (congr_fun (congr_arg Prod.snd hk) i), fun i _ _=> congr_fun hv i⟩
  have hp : Room P S T Xa.x := H.laws.data.room
  have ht := Pond.orbit (H.laws.data.localP F X rfl hK hm).sails.fullC.posSemidef I
  have ht' := Pond.orbit (H.laws.data.localP F' X' hy hK' hm').sails.fullC.posSemidef I
  let g (w : Air f G) := raw (W:=W) M X l s o.a Q.table Q.halo J h (bridge (S:=S) F u,w)
  let y (w : Air f G) := raw (W:=W) M X' l s o.a Q.table Q.halo J h (bridge (S:=S) F' u,w)
  have hJ (p q) (eq : swim I p=swim I q) : g p=y q := by
    have hh : Clump Xa Yf (H.unionP s) p q l l R := ⟨he,(observe I).1 eq,fun _ _=> Iff.rfl⟩
    apply congrArg₂ (·*·)
    · exact prod_congr rfl fun b bJ=> congrArg (h b) (forest_energy hh hp b (fresh b bJ))
    · exact M.lands Xa l Yf hh hp Q.buys (Finset.Subset.refl _) H.laws.intake
  change (∫ w,g w ∂X.dice)=∫ w,y w ∂X'.dice
  have hg : Measurable g := (hM X rfl hK).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable y := (hM X' hy hK').comp (measurable_const.prodMk measurable_id)
  have hC : circuit I X.relating=circuit I X'.relating := by
    ext i j
    exact he.same_cov hp (j:Tubular f G) j.property (i:Tubular f G)
  have hY : MeasurePreserving (swim I) X'.dice (arch I X.relating) := by unfold arch; rw [hC]; exact ht'
  calc
    _ = ∫ i,g (spill I i) ∂arch I X.relating := gathered _ (spill_m I) (show MeasurePreserving (swim I) X.dice (arch I X.relating) from ht) (settled I)
          (fun p q h=> (hJ p q h).trans (hJ q q rfl).symm) hg
    _ = ∫ i,y (spill I i) ∂arch I X.relating := integral_congr_ae (ae_of_all _ fun i=> hJ _ _ (show swim I (spill I i)=_ from rfl))
    _ = _ := (Pond.gathered (spill I) (spill_m I) hY (settled I) (f:=y)
          (fun p q h=> (hJ p p rfl).symm.trans (hJ p q h)) hm).symm

end YM.Integration.InletSusceptibility.JointTicket
