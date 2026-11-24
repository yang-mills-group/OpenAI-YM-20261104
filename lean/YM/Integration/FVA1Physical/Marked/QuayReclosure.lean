import YM.Integration.FVA1Physical.Round2.QuayPurchase

/-! Retain the *represented* marked residual of the native Quay construction on
the entire physical history. Its forecast is a countable stencil bank, with a
vanishing hard array. Every failed row of the actual coefficient therefore
survives literally in the residual, including its sign and native address.
The same tracked proposal has the independent Wilson readout comparison. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Quay
open Function Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations FVA2.CityHistory UVNext.CouplingReset
open Comparison.RG02 RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge PertExtension PertExtension.Chart
open Integration.FVA1Physical.Wilson PertExtension.Series.Tested PhysicalNext.Repeat.Roost
open LocalLTE LocalLTE.Vinca LocalLTE.River Push.AbsoluteSums FVA1Physical.Round2.Quay
open Integration.FVA1Physical.Round2
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ} {n : Side} {F : Frame G d}

/-- Site-rooted native jets and pre-division signed failed amplitudes, on the
same support list as the forecast. -/
structure Account (P : Rep G n) (A : Hol G) (full pred : Coefficient F n) (κ ε : ℝ) : Prop where
  full_format : full.Format 0 A P
  predicted_format : pred.Format 0 A P
  alignment : full.support=pred.support
  forced_zero : pred.forced=0
  lawful : (decrement full pred).Format 0 A P
  head : F.coeffSize (full.x-pred.x) ≤ ε
  remainder : ∃ r f : ℕ → ℝ,
    (∀ i,P.p.supBounds 0 (full.support i) (full.regular i-pred.regular i) (r i)) ∧
    (∀ i,0 ≤ f i ∧ ∀ V,‖full.forced i V‖ ≤ f i) ∧
    SumBudget (fun i=>P.p.mass (full.support i) (r i)) ε ∧
    SumBudget (fun i=>P.p.mass (P.activities.forced i).support (f i/κ)) ε

theorem exhibition_account (P : Rep G n) (A : Hol G) (Z Q : Coefficient F n) (D : SectionData F)
    (k κ v ε : ℝ) (ℓ j : ℕ) (format : Z.Format 0 A P) (ex : Exhibition D k ℓ j A P Z Q κ v ε) :
    Account P A Z Q κ ε := by
  obtain ⟨r,rd,rb⟩ := ex.fee.regular
  obtain ⟨f,fd,fb⟩ := ex.fee.forced
  refine ⟨format,ex.format,ex.layout,ex.stock.forced,ex.trade,ex.canon,r,f,rb,?_,rd,?_⟩
  · intro i
    have h : (decrement Z Q).forced i=Z.forced i := by
      change (Z.forced-Q.forced) i=Z.forced i
      rw [ex.stock.forced,sub_zero]
    simpa only [h] using fb i
  have scaled := budget_scale (inv_pos.mpr ex.fee.divisor).le fd
  convert! scaled using 1
  · funext i; unfold BudgetPoint.mass; ring
  · field_simp [ex.fee.divisor.ne']

variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (P : Bolt A)
variable (ref : ℕ → ℕ) (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n)
local notation "H" => Issue.trail P

def ReclosedLibrary (p d c : ℕ) : Prop :=
  ∀ N n m : ℕ,m<N → ref 0 ≤ m →
  ∀ {I : Type} [Fintype I] [DecidableEq I] (B : Census I) (h : I → ℕ),
  Fintype.card I ≤ c → (∀ j,h j ≤ d) → (∀ j,ref (h j) ≤ m) →
  ∀ (_ : ∀ i : ℕ,LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n))),
  ∃ (Z Q : voiceBall h G → B.Mode → ∀ i,Coefficient ((frames G).level 0) ((H).S.side i n)),
  ∀ i,m ≤ i → ∀ hi:i ≤ N,
    let C := YM.Family.mk H (hol G) (frames G) (localSection G) ref fields
    let β := if i=N then ((H).rep N n N).beta else ((H).rep N n (i+1)).beta
    let κ := Real.sqrt (A.B.a.clock.forcedAllowance i)
    (∀ v s,Account ((H).rep N n i) (hol G) (Z v s i) (Q v s i) κ (Spool.powerR (p+1) β) ∧
      (fun U=>(vista (P:=P) (N:=N) (n:=n) B h v.val i hi U).part s) =
        (Z v s i).density 0 (localSection G 0) ((H).rep N n i) ∧
      (i<N → (Z v s i).density 0 (localSection G 0) ((H).rep N n i) =
        ((H).levels.clock.op i n).push ((H).β N n (i+1)) ((Z v s (i+1)).density 0 (localSection G 0) ((H).rep N n (i+1))))) ∧
    ∀ (T : Slices (H).levels n) (room : (traversal T hi).Room G) (tag : (traversal T hi).Tags)
      (u : Pins G ((H).S.side i n)) (χ : ChartRatio G),LocalRatio χ →
      ∀ (s : B.Mode) (L : ℂ →L[ℝ] ℝ) (r : ℕ),
      let g := Pert.Asymptotics.regulatorRun C N n N
      let U := expLinks G _ (g • u)
      ∃ K : ℝ,0 ≤ K ∧ ∀ v : voiceBall h G, flags ((H).rep N n i).p.threshold U=∅ →
        let E := scalarWilsonBank (traversal T hi) room tag u (actualOffset C n N i) χ
          (L ∘ fullProduct (centeredBatch P N n h v.val).wavelengths s.val)
        ‖L ((Q v s i).exponentialEntry 0 (localSection G 0) ((H).rep N n i) U)-peval E r g‖ ≤
          ‖L‖*Spool.powerR p β+K*g^(r+1)

variable {D₀ : Factor A} {a : ℕ → ℝ} {W : Bid.Worth} {l q M j K d₀ c ι p : ℕ} {κ e : ℝ}
    (crew : Bandage.Harmonics D₀ a W P l) {Hₓ : Spool.Heights}
    (orders : Spool.Terms D₀.shape κ (p+1) j l q M K e A.delay Hₓ)
    (span : East.stagnate q 500<l) (reach : ∀ i j,(D₀.target i j).halo=500)

theorem reclosed_of_library (lib : Bandage.Harmonics.Library crew orders span reach ref fields p d₀ c ι)
    (ok : YM.Family.Makes (YM.Family.mk H (hol G) (frames G) (localSection G) ref fields)) :
    ReclosedLibrary P ref fields p d₀ c := by
  intro N n m hm h₀ I _ _ B h card cap fits paths
  choose C _ reads using fun v:voiceBall h G=>(lib N n m hm h₀ I B h v.val paths card cap fits v.property).1
  refine ⟨fun v s i=>(C v s i).X,fun v s i=>proposal (P:=P) i (C v s i) K,?_⟩
  intro i lo hi fam β κ
  constructor
  · intro v s
    have b := (reads v i lo hi).2 s
    refine ⟨exhibition_account _ _ _ _ _ _ _ _ _ _ _ b.full b.ball,funext b.story,?_⟩
    intro ij
    let seed := gValue (N:=N) (P:=P) (n:=n) h s.val v.val
    have live := giddy (N:=N) (P:=P) (n:=n) B h v.val
    have at_i := arms (P:=P) B h v.val i hi s live
    have at_next := arms (P:=P) B h v.val (i+1) ij s live
    rw [←funext b.story,at_i,←funext ((reads v (i+1) (lo.trans (Nat.le_succ i)) ij).2 s).story,at_next]
    exact gust_step H N n N seed ij
  intro T room tag u χ good s L r g U
  obtain ⟨k,hk,deal⟩ := forecast_wilson P B h ref fields T hi room tag u s L ok good r
  exact ⟨k,hk,fun v healthy=>deal v.val v.property _ _ _ _ _ _ _ _ _ ((reads v i lo hi).2 s) healthy⟩

theorem purchased_reclosed_library (G : Gauge) (simple : G.Simple) (p d c order : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (P : Bolt A)
      (ref : ℕ → ℕ) (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n),
    let C := YM.Family.mk (Issue.trail P) (hol G) (frames G) (localSection G) ref fields
    Spec.Calibrated C ∧ C.Makes ∧ (∀ i,order ≤ (A.B.a.budget i).order) ∧ ReclosedLibrary P ref fields p d c := by
  obtain ⟨X,D,A,R,M,Ra,p₀,μ,σ,F,F',W,Z,P,T,der,_pen,_bar,_post,_views,_fame,_timed,
    ref,fields,cal,ok,_bound,Hs,K,l,q,e,Γ,_port,_stately,a,_lower,_broad,hX,hQ,hr,_eld,
    AX,hM,orders,scales,z,hP,_survey,KX,Fx,hY,_scope,_repository,ι,_pack,_lane,lib⟩ :=
    PhysicalNext.Repeat.Legato.engineProducts simple p order d 1 1 c 1 0 0 0 (1/4)
      (κ:=1) zero_lt_one le_rfl le_rfl (by norm_num) 1
  exact ⟨X,D,A,P,ref,fields,cal,ok,der,reclosed_of_library P ref fields Γ hY hX hQ lib ok⟩

end YM.Integration.FVA1Physical.Marked.Quay
