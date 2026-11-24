import YM.LocalTaylorR2.Orbit.Banker
import YM.MergeProof.Tanger
import YM.RG12.Burst.Cotton
import YM.MergeProof.Groom
/-!
 # Purchase for V. Minty.s same Dawn before any size issues. Keep render View number. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable (G: Gauge)
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open YM.LocalTaylorR2
open RG12 Daisy.Charity.RG12
-- `Pungent` adapted from Mallow.Tray; canon `Works` procurement together on this clock not from earlier Run.
abbrev postOrbit {P:Teller G}(X:ConnectedActivityE6.Target G P)(x:ℝ)(L:Side)(μ:ℝ)(T:RG.Stage) :=
    let B:=radiusB x; let a:=betaF G x L
    (∀ c k:ℝ, 0 ≤ c → 0 ≤ k → k ≤ Real.exp (Trio.coverTicket X.halo)*a^ (-(1/8):ℝ) → c ≤ Real.exp (-X.mark L μ x) → ∃ κ, Payments.Rates B (stems μ L G x) c k κ) ∧
    ∀ V:BudgetPoint,V.threshold=Pressure.temp x→V.B=B→Time.Same T V→∀ α:ℝ,|α|≤ P.top.drift+|G.slopeConstant * Real.log L.val| → let f:= YM.Merge.Spicy.opens G V T.clip T.width T.paths α (Time.credit G T * δE x);0≤f→∃ κ,Payments.Rates B (straw μ L G x) (stems μ L G x) f κ
lemma reserveOrbit {P:Teller G}(X:ConnectedActivityE6.Target G P) (L:Side){μ :ℝ}(h:0<μ)(T:RG.Stage): ∀ᶠ x in atTop, postOrbit G X x L μ T:=by
    filter_upwards [mingle (G:=G) L _ (show 0<μ/4 by positivity) (he:=zero_lt_one) (by norm_num : -(1/8:ℝ)<0) (Rate.power.mul_left (Real.exp (Trio.coverTicket X.halo))),
      mingle (G:=G) L _ (show 0<μ/8 by positivity) zero_lt_two (by norm_num : -(1/4:ℝ)<0) Rate.power, offerSp L T (P.top.drift+|G.slopeConstant * Real.log L.val|)] with x hz hv hB
    refine ⟨fun c k hu hk h hh=>hz _ _ hu hk h (by rwa [one_mul,← syrup (μ:=μ) L X]),?_⟩
    intro V hK hf hR α hα f hΩ
    have hs : stems μ L G x= 2*lauge L (μ/8) x 1 G:=by unfold stems lauge; ring_nf
    have hC:0≤ stems μ L G x:=by unfold stems lauge; positivity
    obtain ⟨p,hp⟩:= hv _ f hC hΩ (hB _ hK hf hR α hα) hs.le
    exact ⟨p,show Payments.Rates _ (straw μ L G x) _ _ _ from by rw [show straw μ L G x=2*lauge L (μ/8) x (1/2) G from by unfold straw lauge; ring_nf]; exact hp⟩

def orbitD : Decal G where
    rub P Q E L W μ o U i x:= postOrbit G Q x L μ U ∧ Mallow.Tariff Q L (i+1) μ x ∧
      ((∃ D:Patch, D.Branches P.bind G∧ D.L=L∧ D.J=P.j) → ∀ j ≤ i, YM.LocalTaylorR2.Orbit.pledge Q E L W μ x o U.order U.power j Chi.canonical (CalendarStep.loss i))
    good P Q E:=by
       obtain ⟨n,h⟩:= Orbit.portion P Q E; refine ⟨n,fun L hL W μ o U i _ hW hμ=>?_⟩
       by_cases he:(∃ D:Patch, D.Branches P.bind G ∧ D.L=L∧D.J=P.j); swap
       · filter_upwards [reserveOrbit G Q L hμ U,Mallow.thaws Q L (i+1) μ hμ] with x hx h; exact ⟨hx,h,fun hf=>False.elim (he hf)⟩
       let ℓ:= CalendarStep.loss i; have hi:0<ℓ:= by unfold ℓ CalendarStep.loss; positivity
       have hv(k:Fin (i+1)):= h L hL W μ o U.order U.power k.val Chi.canonical ℓ hi hW hμ he
       filter_upwards [reserveOrbit G Q L hμ U,Mallow.thaws Q L (i+1) μ hμ,eventually_all.mpr hv] with x hx ht hg; exact ⟨hx,ht,fun h j hj=> hg ⟨j,Nat.lt_succ_of_le hj⟩⟩
-- purchased all parameters Uniform
variable {G}{s: Sheet G}{K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ}
    (R:Register D p u l) {Z:Delays Θ}
lemma minted_same (hx : Mallow.RG12.Earned (orbitD G) R Z) : Minty R (fun i=>i+1) Z:= ⟨fun _ _ hp _ hi=> hx _ _ hp _ hi|>.1,fun _ _ hp _ hi=> hx _ _ hp _ hi|>.2.1⟩
end YM.PhysicalNext.Repeat.Mallow
