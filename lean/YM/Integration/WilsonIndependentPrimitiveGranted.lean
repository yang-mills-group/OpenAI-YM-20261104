import YM.Integration.WilsonIndependentPrimitiveStroll

/-! The actual raw Wilson on-cell primitive has a positive-rank exponential grant at any bought date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitiveGranted
open Function Filter Lattice Laurent Bloch RG Wilson RegulatorIR RegulatorIR.Oracle RegulatorIR.Profiles
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Diagram RegulatorIR.Budget
open RegulatorIR.Budget.Packet RegulatorIR.Halo RegulatorIR.Binding RegulatorIR.Calibration
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonIndependentSpoutOrdinarySpring (peg)
open WilsonIndependentSpoutFiniteStencil (Raw Keys fold)
open WilsonIndependentSpoutOrdinaryPrimitives (board liftKey)
open WilsonIndependentPrimitiveTranslations (roots)
open WilsonIndependentPrimitiveStroll (cell)
open WilsonIndependentConditionalNativeLinks (joint)
open WilsonIndependentPrimitiveCoordinates (printed jo)
open scoped BigOperators Classical Topology

def keys (P:Patch):Finset Branchix:=
  (Finset.univ.image (fun b:Edge (Site P.L)=>Sum.inl (peg b)))∪
    (Finset.univ.image (fun a:Axis=>Sum.inr ((0:Cover),a)))

theorem front (P:Patch)(b:Branchix):∃a∈keys P,∃s:Cover,b=roots P s a:=by
  rcases b with ⟨x,i⟩|⟨x,i⟩
  · let a:Edge (Site P.L):=(wrap P.L x,i)
    obtain ⟨s,hs⟩:=WilsonIndependentPrimitiveOrbit.fibre P.L (wrap_lift (wrap P.L x))
    refine ⟨Sum.inl (peg a),Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩),
      s,congr_arg Sum.inl (Prod.ext hs rfl)⟩
  exact ⟨Sum.inr (0,i),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),
    x,congr_arg Sum.inr (Prod.ext (add_zero x).symm rfl)⟩

theorem sameSize {ι α:Type}[Fintype ι](n:Side)(a:Site n)(x:ι → Co n α):
    soar (tor n) (jog a∘x)=soar (tor n) x:=by
  have h (i j:ι):(tor n).gap (jog a (x i)).1 (jog a (x j)).1=(tor n).gap (x i).1 (x j).1:=
    by apply congr_arg (fun t=>size (lift t));change (a+(x j).1)-(a+(x i).1)=(x j).1-(x i).1;abel
  exact le_antisymm
    (league_le _ _ fun i j=>(h i j).le.trans (leg_le (tor n) (Prod.fst∘x) i j))
    (league_le _ _ fun i j=>(h i j).ge.trans (leg_le (tor n) (Prod.fst∘(jog a∘x)) i j))

theorem actual {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Z:∀P:Patch,P.Branches K G)(t:Page M→Scale)(f:Flap M)(e r:ℕ):
    let P:=C.pactP f;let T:=C.bore G Z t f
    ∃D:ℕ,∀ᶠ n:Side in atTop,∀x,printed P T e r n x≠0→soar (tor n) x≤D:=by
  classical
  intro P T
  let S:=C.rail K f
  let bags (b:Branchix):Finset (Tuple (KFoot G) r):=((C.wheeled G Z t f b).sized e r).toFinset
  let cache:Finset (Tuple (KFoot G) r):=(keys P).biUnion bags
  refine ⟨cache.sup (fun z=>soar terrain (joint G P∘z)),?_⟩
  have hx:∀ᶠ n:Side in atTop,∀z∈cache,soar (tor n) (foldUnder n∘(joint G P∘z))=soar terrain (joint G P∘z):=
    (eventually_all_finset cache).mpr fun z _=>touched (joint G P∘z)
  filter_upwards [hx] with n hit
  intro x nx
  let ω:Tuple (Raw G (n*P.L)⊕Raw G n) r:=(jo G P n).symm∘x
  obtain ⟨b,hb⟩:∃b:Keys P n,cell P n T e r (liftKey b) ω≠0:=by
    by_contra! all
    apply nx
    simp only [printed, WilsonIndependentSpoutOrdinaryPrimitives.board,Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _=>all i
  obtain ⟨z,wrapZ,hz⟩:∃z:Tuple (KFoot G) r,fold P n∘z=ω ∧ T (liftKey b) e r z≠0:=by
    by_contra! all
    apply hb
    let Ω:=Stalk (fun k:Tuple (KFoot G) r=>fold P n∘k) ω
    have zall:(fun j:Ω=>T (liftKey b) e r j.val)=fun _=>(0:ℝ):=funext fun j=>all j.val j.property
    change (∑' j:Ω,T (liftKey b) e r j.val)=0
    rw [zall];exact tsum_zero
  obtain ⟨a,ha,s,hs⟩:=front P (liftKey b)
  let v:Tuple (KFoot G) r:=(bundleS S s).symm∘z
  have moved:T (roots P s a) e r=echo (bundleS S s) (T a e r):=
    congr_fun (WilsonIndependentPrimitiveTranslations.original C Z t f s a e) r
  have act:T a e r v≠0:=by rw [hs,moved] at hz;exact hz
  have inside:v∈cache:=Finset.mem_biUnion.mpr ⟨a,ha,by change v∈((C.wheeled G Z t f a).sized e r).toFinset;rw [Set.Finite.mem_toFinset];exact act⟩
  have rep:x=jog (wrap n s)∘(foldUnder n∘(joint G P∘v)):=by
    funext j
    have w:fold P n (z j)=(jo G P n).symm (x j):=congr_fun wrapZ j
    have commute:=WilsonIndependentPrimitiveCoordinates.translation S s (v j)
    change joint G P ((bundleS S s) ((bundleS S s).symm (z j)))=jog s (joint G P (v j)) at commute
    rw [Equiv.apply_symm_apply] at commute
    change x j=jog (wrap n s) (foldUnder n (joint G P (v j)))
    rw [←fold_move,←commute,←WilsonIndependentPrimitiveCoordinates.wrapping,w,Equiv.apply_symm_apply]
  rw [rep,sameSize,hit _ inside]
  exact Finset.le_sup (f:=fun z=>soar terrain (joint G P∘z)) inside

theorem original {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(e r:ℕ)(pin:Fin r):
    let P:=C.pactP f;let T:=C.bore G Z (sheet D) f
    Yields (printed P T e r) (fun x=>((C.dialect Y G Z (sheet D)).frames f).addon e r ((joint G P).symm∘x)):=by
  intro P T
  obtain ⟨d,hd⟩:=actual C Z (sheet D) f e r
  apply WilsonIndependentPrimitiveWidth.original pin d _ _ hd
  · intro x
    have h:=WilsonIndependentPrimitiveCoordinates.point C Y Z D f e r pin x
    dsimp only at h
    exact tendsto_const_nhds.congr' (h.mono fun _ hz=>hz.symm)
  exact Eventually.of_forall fun n=>WilsonIndependentPrimitiveStroll.original C Z (sheet D) f n e r

end YM.Integration.WilsonIndependentPrimitiveGranted
