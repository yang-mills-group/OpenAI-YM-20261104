import YM.Integration.WilsonReflectedMicroscopicSites

/-! On the elected Wilson family the three input trajectories may follow
different child residues. Their reflected product is filed as one physical
coefficient, on the original period, before testing the older field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedThermometerCapture
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Next.Rank Ribbon Trace.Physical
open WilsonThermometerOwnOffsetRadii WilsonReflectedMicroscopicSites
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {I:Type} [Fintype I] [DecidableEq I]
set_option quotPrecheck false
local notation "C" => R.family
local notation "H" => R.family.path
local notation "δ" => renal R.alloy.B.a
local notation "X" => bling R.alloy.B.a

include simple book in
theorem original (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) :
  ∃ t ≥ D+3,∀ᶠ k in atTop,∀ (p N m J h:ℕ) (kn:k < N) (jm : J ≤ m) (mk:m+1 ≤ k)
    (_ : R.family.ref h ≤ m) (i₀ : I)
    (d:I → ℕ) (_ : ∀i,d i ≤ D) (z:I → Site (R.family.side N p))
    (V:(i:I) → Sight R.family (d i) p) (r:(i:I) → Emblems R.family (d i))
    (_ : ∀i,WilsonThermometerOffsetTrajectory.Enrolled R.makes R.doors
      (WilsonThermometerOffsetLedger.cash R) k N p (d i)
      (WilsonThermometerOffsetResidue.digits R N p (z i)) (V i) (r i))
    (y:(i:I) → Palette R.family (d i)) (_ : ∀i,size (y i) ≤ 1)
    (_ : WilsonThermometerOwnOffsetNectar.location R (z i₀) (m+1)=0),
    let o := site (J:=J) R z
    let B := R.family.path.levels.budget
    (∀ a, m+1 ≤ a → a ≤ k → Cross (B a).B (o a)) →
    (∀a b,a≠b → (B k).B^2 < separation (o k a) (o k b)) →
    ∀ (l:ℕ) (α Z:ℝ) (_ : 0 < α) (_ : α ≤ 1)
      (_ : ∀a,m+1 ≤ a → a < k → α ≤ license H δ (Fintype.card I) (carpet H a) (a+1))
      (_ : α ≤ license H δ (Fintype.card I) l (m+1))
      (_ : ∀i:Site (R.family.side J p)×I,coverNumber (B (m+1)).B
        ({o (m+1) (i.1,i₀),o (m+1) i}:Support _) ≤ l)
      (_ : 0 < Z) (_ : Z ≤ α^(Fintype.card I)*compensation H (Fintype.card I) (m+1) k 0 α
        (∏ _i:I,δ k*radius R t k (k+1)/8))
      (w:Site (R.family.side J p) → ℝ) (_ : ∀i,0 < w i) (_ : ∀i,w i ≤ δ m*(Z/(16*X m))),
    let mn := m.le_succ.trans (mk.trans kn.le)
    let field := fun U => ∏ i,WilsonThermometerIntrinsicRoster.source R d z y r kn.le i U
    let tariff := R.family.S.a (m+1)^h*(X m*(4*(1/Z)))
    ∃ q:Trace.Physical.GermGraph.store R.family h p m,
      RG16.Literal.Fleet R.family N p h m J field (jm.trans mn) w q mn ∧
      Trace.Physical.GermGraph.reads h N p m q tariff ∧
      (R.family.labels.level h).coeffSize q.x ≤ tariff ∧
      RG16.Literal.credit R.family N p h field m mn=Trace.Physical.GermGraph.value («C» := R.family) h N p m q :=by
  obtain ⟨t,ht,arms⟩:=WilsonReflectedMicroscopicSites.entered (I:=I) R simple shop D
  refine ⟨t,ht,arms.mono ?_⟩
  intro k hk p N m J h kn jm mk live i₀ d cap z V r admitted y hy anchor0 _ _ cross spaced
    l α Z pos unit money launch cover posZ funds w hw wage
  let mn:=m.le_succ.trans (mk.trans kn.le)
  let jn:=jm.trans mn
  let T:=center R.family.S p jn 0
  let f:=WilsonThermometerIntrinsicRoster.source R d z y r kn.le
  let F (x:Site (R.family.side J p)×I):=T.copy x.1 (f x.2)
  let E:=Mix.camp R.family p J
  let P:=hands R.family p J
  let o:=site (J:=J) R z
  have cont(i:I):Continuous (f i):=(R.family.continuousO N p (d i) _ (z i)).const_smul ((R.family.S.a k:ℂ)^(d i))
  have copied(i:Site (R.family.side J p)×I):Continuous (F i):=
    cappedC C J p N jn (fun _=>f i.2) (i.1,true) (cont _)
  have starts : (R.family.path.rep N p N).eval = bare (R.family.beta N p) := (R.makes.wilson.starts N p).2
  have integr:Integrable (birth (Names (Site (R.family.side J p)) I) (R.family.path.rep N p N) F) (prior G _):=
    (hatCont C N p F copied (show Continuous (R.family.path.rep N p N).eval by
      rw [starts];exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have same (a:Site (R.family.side J p)) (i:I) : F (a,i)=stepUp (P a) (E N a) (F (0,i)):=by
    have h0 : F (0,i)=f i := funext (T.copy_zero (f i))
    rw [h0]
    exact (MergeProof.handmove C N p J jn _ a).symm
  have scrim:=(R.again simple).1.scrim
  obtain ⟨χ,cuts⟩:=book.productCuts.mother
  have occupancy (a:ℕ) (ja:J ≤ a):Occupancy (E a) (mutt R.alloy.B.a R.Q m):= fun v=>
    (Occupancy.of_injective (show Injective (E a) by
      rw [show E a=(R.family.S.toDepth ja p).embed from funext (elev C J p a ja)]
      exact (R.family.S.toDepth ja p).embed_injective) v).trans (scrim.back m)
  have grouped:=WilsonReflectedArmsCapture.original C N p m k h E o P 0 (fun i=>Equiv.swap 0 i)
    i₀ w (fun a (_ : I)=>radius R t k a) F mk kn R.makes scrim live (cuts h)
    (WilsonReflectedMicroscopicSites.joint R z simple k t spaced) (fun _=>radius_pos R t k (k+1) k.le_succ)
    (hk p N kn.le J jn d cap z V r admitted y hy)
    (Ribbons.uphill C J m p N jm) (P_on C J p) (zeroMama C J p m jm)
    (anchor R z (jm.trans m.le_succ) (mk.trans kn.le) i₀ anchor0)
    (fun i _=>Equiv.swap_apply_left ..)
    (fun a ha hN=>collar R z (jm.trans (m.le_succ.trans ha)) hN)
    (fun a _ hak=>adjacent (J:=J) R z (hak.trans kn)) cross (fun a b ne=>(spaced a b ne).le)
    (fun i _ b=>same i b) integr (occupancy m jm) (occupancy (m+1) (jm.trans m.le_succ))
    pos unit money launch cover posZ funds hw wage
  obtain ⟨q,fmt,rem,price,served⟩:=book.literal.bridge C N p h m P (E m) w _ grouped
  let field (U):=∏ i,f i U
  have copied_product : (fun a (U:Config G (R.family.side N p))=>∏ i,F (a,i) U) =
      fun a=>T.copy a field :=by
    funext a U
    unfold F field Tiling.copy
    split_ifs <;> simp only [star_prod]
  rw [copied_product] at served
  exact ⟨q,served,⟨fmt,rem⟩,price,RG16.Literal.Fleet.keeps C N p h m J R.makes field
    (continuous_finsetProd _ (fun i _=>cont i)) jm mn w q ⟨fmt,rem⟩ served⟩
end YM.Integration.WilsonReflectedThermometerCapture
