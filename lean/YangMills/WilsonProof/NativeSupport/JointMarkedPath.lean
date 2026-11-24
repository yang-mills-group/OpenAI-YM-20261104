import YangMills.WilsonProof.NativeSupport.JointMarkedHaar
import YangMills.WilsonProof.NativeSupport.JointHistoryTilt

/-! The same actual marked Haar push at each date, with the original
descent, one shared tag at each bond, and the original noise normalizer.
The selected subset contains blocking energies only. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointMoments
open Function Finset Lattice RG Pressure Wilson Tree RGComparison.Core16 Push.BetaTransport Push.SectorMeasure MeasureTheory
open WilsonUniformUnmarkedInletEnergySites
open scoped Classical BigOperators Topology
variable {G:Gauge} {n c f:Side}

def kineticOnly {n:Side} : {c:Side} → (d:Descent n c) → Finset (sites n d) → Prop
  | _,.nil,I=>I=∅
  | _,.push _ _ d,I=>kineticOnly d I.toRight

def markedOutput {G:Gauge} {n:Side} : {c:Side} → (d:Descent n c) → (ℕ → ℝ) → (Config G n → ℝ) →
    Finset (sites n d) → (sites n d → ℝ → ℝ) → Config G c → ℝ
  | _,.nil,β,g,_,_=>fun V=>bare (β 0) V*g V
  | _,.push S _ d,β,g,I,h=>JointPhysical.push S I.toLeft (h ∘ Sum.inl) (β 1)
      (markedOutput d (Descent.upβ β) g I.toRight (h ∘ Sum.inr))

def payload (d:Descent n c) (I:Finset (sites n d)) (h:sites n d → ℝ → ℝ)
    (t:d.Tags) (V:Config G c) (x:Descent.Fields G d) :=
  ∏ q∈I,h q (cell G d t V x q)

private theorem compact_envelope {X:Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {g:X → ℝ} (hg:Continuous g) : Envelope g :=
  ⟨hg.measurable,let z:=isCompact_univ.exists_bound_of_continuousOn hg.continuousOn;
    ⟨z.choose,fun x=>z.choose_spec x (Set.mem_univ _)⟩⟩

private theorem pull_envelope {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f:Y → ℝ} {t:X → Y} (hf:Envelope f) (ht:Measurable t) : Envelope (f ∘ t) :=
  ⟨hf.meas.comp ht,hf.cost.choose,fun x=>hf.cost.choose_spec (t x)⟩

theorem marked_regular (d:Descent n c) (ok:d.OK G) (β:ℕ → ℝ) {g:Config G n → ℝ} (cg:Continuous g)
    (sym:GaugeInvariant g) (I:Finset (sites n d)) (h:sites n d → ℝ → ℝ)
    (hm:∀ q∈I,Measurable (h q)) (hu:∀ q∈I,∀ z∈Set.Icc 0 (cap d q),‖h q z‖ ≤ 1) :
    Envelope (markedOutput d β g I h) ∧ GaugeInvariant (markedOutput d β g I h) := by
  induction d generalizing β with
  | nil => exact ⟨compact_envelope ((bare_cont (β 0)).mul cg),fun t U=>congrArg₂ (·*·) (bare_gauge ..) (sym t U)⟩
  | @push m i S T d ih =>
    let lower:=markedOutput d (Descent.upβ β) g I.toRight (h ∘ Sum.inr)
    have orig:=ih ok.2 (Descent.upβ β) I.toRight (h ∘ Sum.inr) (fun q hit=>hm (.inr q) (mem_toRight.mp hit))
      (fun q hit=>hu (.inr q) (mem_toRight.mp hit))
    have meas b (hb:b∈I.toLeft) := hm (.inl b) (mem_toLeft.mp hb)
    have unit b (hb:b∈I.toLeft) := hu (.inl b) (mem_toLeft.mp hb)
    exact ⟨JointPhysical.push_envelope S I.toLeft (h ∘ Sum.inl) (β 1) ok.1 orig.1 meas unit,
      JointPhysical.push_gauge S I.toLeft (h ∘ Sum.inl) (β 1) ok.1 orig.1 meas unit orig.2⟩

theorem payload_envelope (d:Descent n c) (ok:d.OK G) (t:d.Tags) (I:Finset (sites n d)) (h:sites n d → ℝ → ℝ)
    (hm:∀ q∈I,Measurable (h q)) (hu:∀ q∈I,∀ z∈Set.Icc 0 (cap d q),‖h q z‖ ≤ 1) :
    Envelope fun z:Config G c × Descent.Fields G d=>payload d I h t z.1 z.2 := by
  refine ⟨Finset.measurable_fun_prod _ (fun q hit=>(hm q hit).comp (cell_envelope d ok t q).meas),1,fun z=>?_⟩
  unfold payload
  rw [norm_prod]
  exact prod_le_one (fun q _=>norm_nonneg _) (fun q hit=>hu q hit _ (bounded d t z.1 z.2 q))

variable {S:StepData c f} {T:Forest S.ratio} {D:Descent n f}
theorem payload_split (I:Finset (sites n (Descent.push S T D))) (h:sites n (Descent.push S T D) → ℝ → ℝ)
    (a:S.Choices) (b:D.Tags) (V:Config G c) (U:T.Slice G) (x:Descent.Fields G D) :
    payload (.push S T D) I h (a,b) V (Sum.elim U x) =
      JointPhysical.sample S a I.toLeft (h ∘ Sum.inl) (T.drape U) V*
      payload D I.toRight (h ∘ Sum.inr) b (T.drape U) x := by
  let φ (q:Bond c ⊕ sites n D):=h q (cell G (.push S T D) (a,b) V (Sum.elim U x) q)
  calc
    _ = ∏ q∈I.toLeft.disjSum I.toRight,φ q :=
      congrArg (fun K:Finset (Bond c ⊕ sites n D)=>∏ q∈K,φ q) Finset.toLeft_disjSum_toRight.symm
    _ = _ := by rw [prod_disjSum];rfl

private theorem append_integral {g:Descent.Fields G (Descent.push S T D) → ℝ}
    (hg:Integrable g ((Descent.push S T D).measure G)) :
    ∫ z,g z ∂((Descent.push S T D).measure G) = ∫ u,∫ z,g (Sum.elim u z) ∂D.measure G ∂T.order G := by
  let e:=MeasurableEquiv.sumPiEquivProdPi (fun _ : T.Free ⊕ D.Links=>G.El)
  have mp:MeasurePreserving e.symm ((T.order G).prod (D.measure G)) ((Descent.push S T D).measure G) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _=>G.probHaar)
  exact (mp.integral_comp' g).symm.trans (integral_prod _ ((mp.integrable_comp_emb e.symm.measurableEmbedding).mpr hg))

private theorem integrand_split (β:ℕ → ℝ) (a:S.Choices) (b:D.Tags) (g:Config G n → ℝ)
    (V:Config G c) (U:T.Slice G) (x:Descent.Fields G D) :
    (Descent.push S T D).integrand β (a,b) g V (Sum.elim U x) =
      (S.likelihood (T.drape U) a*Real.exp (-(β 1*tagEnergy S a (T.drape U) V)))*
        D.integrand (Descent.upβ β) b g (T.drape U) x := by
  unfold Descent.integrand
  rw [Descent.account,Descent.probability,Descent.fine]
  dsimp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,Prod.fst,Prod.snd]
  rw [neg_add,Real.exp_add]
  ring

private theorem tagged_factor (β:ℝ) (a:S.Choices) (U:Config G f) (V:Config G c) :
    taggedKernel S β a U V=Next.Fluctuations.Sector.prefactor S G β*
      (S.likelihood U a*Real.exp (-(β*tagEnergy S a U V))) := by
  unfold taggedKernel
  rw [noise_factor]
  unfold tagEnergy Gibbs.factor
  rw [neg_mul,mul_left_comm]

private theorem weighted_held (d:Descent n c) (ok:d.OK G) (β:ℕ → ℝ) {g:Config G n → ℝ} (cg:Continuous g)
    (I:Finset (sites n d)) (h:sites n d → ℝ → ℝ) (hm:∀ q∈I,Measurable (h q))
    (hu:∀ q∈I,∀ z∈Set.Icc 0 (cap d q),‖h q z‖ ≤ 1) (t:d.Tags) (V:Config G c) :
    Envelope (fun x:Descent.Fields G d=>payload d I h t V x*d.integrand β t g V x) := by
  let a (z:Config G c × Descent.Fields G d):=payload d I h t z.1 z.2*d.integrand β t g z.1 z.2
  have ea:Envelope a:=(payload_envelope d ok t I h hm hu).mul (d.path_envelope ok β t g cg)
  exact pull_envelope (f:=a) (t:=fun x:Descent.Fields G d=>(V,x)) ea (measurable_const.prodMk measurable_id)

theorem strictly_interior_kinetic (d:Descent n c) (I:Finset (sites n d)) (old:∀ q∈I,lag d q < d.depth) : kineticOnly d I := by
  induction d with
  | nil =>
    apply eq_empty_iff_forall_notMem.mpr
    intro q hit
    exact (Nat.not_lt_zero _) (old q hit)
  | push S T d ih =>
    apply ih
    intro q mem
    exact Nat.lt_of_succ_lt_succ (old (.inr q) (mem_toRight.mp mem))

theorem marked_path_formula (d:Descent n c) (ok:d.OK G) (β:ℕ → ℝ) {g:Config G n → ℝ}
    (cg:Continuous g) (sym:GaugeInvariant g) (I:Finset (sites n d)) (h:sites n d → ℝ → ℝ)
    (hm:∀ q∈I,Measurable (h q)) (hu:∀ q∈I,∀ z∈Set.Icc 0 (cap d q),‖h q z‖ ≤ 1)
    (kin:kineticOnly d I) (V:Config G c) :
    markedOutput d β g I h V=d.scalar G β*∑ t,∫ x,payload d I h t V x*d.integrand β t g V x ∂d.measure G := by
  induction d generalizing β with
  | nil =>
    change I=∅ at kin
    subst I
    let D₀:Descent n n:=.nil
    have base (x:Descent.Fields G D₀):D₀.integrand β () g V x=bare (β 0) V*g V := by
      unfold D₀
      simp only [Descent.integrand,Descent.probability,Descent.account,Descent.fine,bare,neg_mul,one_mul]
    change bare (β 0) V*g V=1*∑ t:Unit,∫ x,payload D₀ ∅ h t V x*D₀.integrand β t g V x ∂D₀.measure G
    rw [one_mul,Fintype.sum_unique]
    simp only [payload,prod_empty,one_mul,show (default:Unit)=() from rfl,base,integral_const,probReal_univ,one_smul]
  | @push m i S T d ih =>
    let D:=Descent.push S T d
    let lo:=Descent.upβ β
    let K:Finset (Bond m):=I.toLeft
    let J:Finset (sites n d):=I.toRight
    let u:=h ∘ Sum.inl (β:=sites n d)
    let h':=h ∘ Sum.inr (α:=Bond m)
    let g':=markedOutput d lo g J h'
    let non g₀ (U:T.Slice G):=S.likelihood (T.drape U) g₀*Real.exp (-(β 1*tagEnergy S g₀ (T.drape U) V))
    let z₀ (a:S.Choices) (U:T.Slice G):=JointPhysical.sample S a K u (T.drape U) V
    let row (b:d.Tags) (U:T.Slice G) (x:Descent.Fields G d):=payload d J h' b (T.drape U) x*d.integrand lo b g (T.drape U) x
    let body (a:S.Choices) (b:d.Tags) (x:Descent.Fields G D):=payload D I h (a,b) V x*D.integrand β (a,b) g V x
    have lower:=marked_regular d ok.2 lo cg sym J h' (fun q hit=>hm (.inr q) (mem_toRight.mp hit))
      (fun q hit=>hu (.inr q) (mem_toRight.mp hit))
    have lowerEq:=ih ok.2 lo J h' (fun q hit=>hm (.inr q) (mem_toRight.mp hit))
      (fun q hit=>hu (.inr q) (mem_toRight.mp hit)) kin
    have factor (a:S.Choices) (b:d.Tags) (U:T.Slice G) (x:Descent.Fields G d) :
        body a b (Sum.elim U x)=(z₀ a U*non a U)*row b U x := by
      dsimp only [body,D]
      rw [payload_split,integrand_split]
      dsimp only [z₀,non,row,J,K,u,h',lo]
      ring
    have inner (a:S.Choices) (b:d.Tags) (U:T.Slice G):
        (∫ x,body a b (Sum.elim U x) ∂d.measure G)=(z₀ a U*non a U)*∫ x,row b U x ∂d.measure G := by
      simp_rw [factor,integral_const_mul]
    have e (a:S.Choices) (b:d.Tags):Envelope (body a b) :=
      weighted_held D ok β cg I h hm hu (a,b) V
    have jr (a:S.Choices) (b:d.Tags) : Integrable (fun U:T.Slice G=>∫ x,body a b (Sum.elim U x) ∂d.measure G) (T.order G) := by
      have join : Measurable (fun z:T.Slice G × Descent.Fields G d=>(Sum.elim z.1 z.2 : Descent.Fields G D)) := by
        refine measurable_pi_lambda _ ?_
        intro j
        cases j
        · exact (measurable_pi_apply _).comp measurable_fst
        · exact (measurable_pi_apply _).comp measurable_snd
      exact ((pull_envelope (e a b) join).integrable ((T.order G).prod (d.measure G))).integral_prod_left
    have pay (a:S.Choices) (U:T.Slice G) : JointPhysical.integrand S a K u (β 1) g' V (T.drape U)=
        D.scalar G β*∑ b:d.Tags,∫ x,body a b (Sum.elim U x) ∂d.measure G := by
      change (taggedKernel S (β 1) a (T.drape U) V * markedOutput d lo g J h' (T.drape U))*z₀ a U=_
      rw [tagged_factor,lowerEq]
      simp_rw [inner]
      rw [←mul_sum]
      change (_*non a U*(d.scalar G lo*∑ b:d.Tags,∫ x,row b U x ∂d.measure G))*z₀ a U=
        (Next.Fluctuations.Sector.prefactor S G (β 1)*d.scalar G lo)*((z₀ a U*non a U)*_)
      ring
    change (∑ a:S.Choices,∫ Z,JointPhysical.integrand S a K u (β 1) g' V Z ∂prior G i)=
      D.scalar G β*∑ t:S.Choices × d.Tags,∫ x,body t.1 t.2 x ∂D.measure G
    conv_rhs => rhs; rw [Fintype.sum_prod_type]
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [JointPhysical.pack S a K u T (β 1) V ok.1 lower.1 lower.2
      (fun q mem=>hm (.inl q) (mem_toLeft.mp mem)) (fun q mem=>hu (.inl q) (mem_toLeft.mp mem))]
    change (∫ U,JointPhysical.integrand S a K u (β 1) g' V (T.drape U) ∂T.order G)=_
    rw [show (fun U:T.Slice G=>JointPhysical.integrand S a K u (β 1) g' V (T.drape U)) =
      fun U:T.Slice G=>D.scalar G β*∑ b:d.Tags,∫ x,body a b (Sum.elim U x) ∂d.measure G from funext (pay a),integral_const_mul]
    rw [integral_finsetSum _ (fun b _=>jr a b)]
    apply congrArg (D.scalar G β*·)
    exact sum_congr rfl fun b _=>(append_integral ((e a b).integrable _)).symm

end YM.Integration.InletSusceptibility.JointMoments
