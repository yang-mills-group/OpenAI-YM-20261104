import YM.Integration.FVA1Physical.Marked.QuayPanel
import YM.Integration.FVA1Physical.Marked.QuayBasis
import YM.Integration.FVA1Physical.Marked.QuayInherited

/-! The prescribed mixed physical target now has one actual stencil bank and
one forecast bank for all independent complex tests. The bank is selected
before the test and before any configuration, with no tensor-basis factor. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Quay
open Function Finset MeasureTheory Lattice RG YM.Wilson Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations UVNext.CouplingReset
open Integration.FVA1Physical.Round2 Integration.FVA1Physical.Round2.Quay LocalLTE.Vinca PhysicalNext.Repeat.Roost
open scoped Classical BigOperators

theorem combined_density {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {R : Rep G n}
    {J : Type} [Fintype J] (index : ℕ ≃ J × ℕ) (Z : J → Coefficient F n) (w : J → ℂ)
    {κ σ C Λ δ v : ℝ} (hk : 0<κ) (law : R.Lawful σ C Λ δ v) {e : J → ℝ}
    (finite : ∀ j,(Z j).remBound 0 R κ (e j)) (D : SectionData F) (U : Config G n) :
    (combine index Z w).density 0 D R U = ∑ j,w j*(Z j).density 0 D R U := by
  have h := merge_density index (fun j=>stretch (w j) (Z j)) hk law (fun j=>stretch_rem _ (finite j))
    (hasSum_fintype _).summable (hasSum_fintype _).summable D U
  change (merge index (fun j=>stretch (w j) (Z j))).density 0 D R U = _
  rw [←h.tsum_eq,tsum_fintype]
  exact sum_congr rfl fun _ _=>stretch_density ..

variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (P : Bolt A) (ref : ℕ → ℕ)
local notation "H" => Issue.trail P

def tensorIndex {I : Type} [Fintype I] [DecidableEq I] (B : Census I) {d : ℕ} (h : I → Fin (d+1)) (s : B.Mode) : ℕ ≃ Pure (G:=G) B h s × ℕ := by
  letI : Nonempty (Pure (G:=G) B h s) := ⟨fun _=>0⟩
  exact Extra.Histories.code _

def UniformTensor (p d c : ℕ) : Prop :=
  ∀ N n m : ℕ,m<N → ref 0 ≤ m →
  ∀ {I : Type} [Fintype I] [DecidableEq I] (B : Census I) (h : I → Fin (d+1)),
  Fintype.card I ≤ c → (∀ j,ref (h j).val ≤ m) →
  ∀ (_ : ∀ i : ℕ,LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n))) (s : B.Mode),
    ∃ (Z Q : Pure (G:=G) B h s → ∀ i,Coefficient ((frames G).level 0) ((H).S.side i n)),
    ∀ i,m ≤ i → ∀ hi:i≤N,∀ v : voiceBall (fun j=>(h j).val) G,
      let e := priceAt P p N n i
      let R := (H).rep N n i
      let w := weights B h s v
      let ix := tensorIndex (G:=G) B h s
      let full := combine ix (fun a=>Z a i) w
      let pred := combine ix (fun a=>Q a i) w
      let Δ := decrement full pred
      full.support=(fun k=>(Z (ix k).1 i).support (ix k).2) ∧ full.support=pred.support ∧
        full.Format 0 (hol G) R ∧ pred.Format 0 (hol G) R ∧ Δ.Format 0 (hol G) R ∧
        ((frames G).level 0).coeffSize Δ.x ≤ e ∧ Δ.remBound 0 R (Real.sqrt (A.B.a.clock.forcedAllowance i)) (2*e) ∧
        (∀ k U,Δ.forced k U=∑ a,w a*(Z a i).forced k U) ∧
        ∀ U,full.density 0 (localSection G 0) R U=(vista (P:=P) (N:=N) (n:=n) B (fun j=>(h j).val) v.val i hi U).part s

variable (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n)
    {D₀ : Factor A} {a : ℕ → ℝ} {W : Bid.Worth} {l q M j K d₀ c ι p : ℕ} {κ e : ℝ}
    (crew : Bandage.Harmonics D₀ a W P l) {Hₓ : Spool.Heights}
    (orders : Spool.Terms D₀.shape κ (p+1) j l q M K e A.delay Hₓ)
    (span : East.stagnate q 500<l) (reach : ∀ i j,(D₀.target i j).halo=500)

theorem tensor_of_library (lib : Bandage.Harmonics.Library crew orders span reach ref fields p d₀ c ι)
    (ok : YM.Family.Makes (YM.Family.mk H (hol G) (frames G) (localSection G) ref fields)) : UniformTensor P ref p d₀ c := by
  intro N n m hm h₀ I _ _ B h card fits paths s
  let u := pureVoice (G:=G) B h s
  choose F orator reads using fun b : Pure (G:=G) B h s=>(lib N n m hm h₀ I B (fun k=>(h k).val) (u b).val paths card (fun k=>Nat.le_of_lt_succ (h k).isLt) fits (u b).property).1
  let Z (b : Pure (G:=G) B h s) i := (F b s i).X
  let Q (b : Pure (G:=G) B h s) i := proposal (P:=P) i (F b s i) K
  refine ⟨Z,Q,?_⟩
  intro i lo hi v e R w ix full pred Δ
  have booked (b : Pure (G:=G) B h s) := (reads b i lo hi).2 s
  have acct (b : Pure (G:=G) B h s) : Account R (hol G) (Z b i) (Q b i) (Real.sqrt (A.B.a.clock.forcedAllowance i)) e :=
    exhibition_account _ _ _ _ _ _ _ _ _ _ _ (booked b).full (booked b).ball
  let b₀ : Pure (G:=G) B h s := fun _=>0
  have hk := (booked b₀).ball.fee.divisor
  have nonnegative : 0 ≤ e := (Work.G08.size_nonneg _ _).trans (acct b₀).head
  obtain ⟨fixed,same,f0,f1,f2,head,res,hard⟩ := common_test_budget ix (fun b=>Z b i) (fun b=>Q b i) w hk acct
  have charge : (∑ a,‖w a‖)*e ≤ e := mul_le_of_le_one_left nonnegative (weight_one B h s v)
  refine ⟨fixed,same,f0,f1,f2,head.trans charge,rem_mono res ?_,hard,?_⟩
  · linarith only [mul_le_mul_of_nonneg_left charge (by norm_num : (0:ℝ)≤2)]
  intro U
  rw [vista_tensor B h s P ref fields ok v hi U]
  have valid := (P.choice.represents N n i hi).good
  have physical := combined_density ix (fun b=>Z b i) w hk valid (fun b=>(orator b s |>.schedule i lo hi).certC.credit) (localSection G 0) U
  refine physical.trans (sum_congr rfl fun b _=>?_)
  exact congrArg (w b*·) ((booked b).story U).symm

theorem purchased_common_tensor (G : Gauge) (simple : G.Simple) (p d c order : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (P : Bolt A)
      (ref : ℕ → ℕ) (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n),
    let C := YM.Family.mk (Issue.trail P) (hol G) (frames G) (localSection G) ref fields
    Spec.Calibrated C ∧ C.Makes ∧ (∀ i,order ≤ (A.B.a.budget i).order) ∧
      ReclosedLibrary P ref fields p d c ∧ FramesReclose P ref p d c ∧ UniformTensor P ref p d c := by
  obtain ⟨X,D,A,R,M,Ra,p₀,μ,σ,F,F',W,Z,P,T,der,_pen,_bar,_post,_views,_fame,_timed,
    ref,fields,cal,ok,_bound,Hs,K,l,q,e,Γ,_port,_stately,a,_lower,_broad,hX,hQ,hr,_eld,
    AX,hM,orders,scales,z,hP,_survey,KX,Fx,hY,_scope,_repository,ι,_pack,_lane,lib⟩ :=
    PhysicalNext.Repeat.Legato.engineProducts simple p order d 1 1 c 1 0 0 0 (1/4)
      (κ:=1) zero_lt_one le_rfl le_rfl (by norm_num) 1
  exact ⟨X,D,A,P,ref,fields,cal,ok,der,reclosed_of_library P ref fields Γ hY hX hQ lib ok,
    reclosed_frames_of_library P ref fields Γ hY hX hQ lib,tensor_of_library P ref fields Γ hY hX hQ lib ok⟩

end YM.Integration.FVA1Physical.Marked.Quay
