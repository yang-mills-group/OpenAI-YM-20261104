import YM.Integration.FVA1Physical.Marked.QuayCore
import YM.Integration.FVA1Physical.Marked.QuayReclosure

/-! All positive-grade singleton frames and the full mixed ledger live on one
calibrated family. Their predicted nonunit coordinate at the next stage agrees,
at the paid accuracy, with the actual engineering-rescaled transport of the
preceding prediction. No transport-error or input-estimate hypothesis is exposed. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Quay
open Function Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations FVA2.CityHistory UVNext.CouplingReset
open Integration.FVA1Physical.Round2 Integration.FVA1Physical.Round2.Quay
open PhysicalNext.Repeat.Roost
open scoped Classical BigOperators
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (P : Bolt A) (ref : ℕ → ℕ)
local notation "H" => Issue.trail P

def priceAt (p N n i : ℕ) := Spool.powerR (p+1) (if i=N then ((H).rep N n N).beta else ((H).rep N n (i+1)).beta)

def FramesReclose (p d c : ℕ) : Prop :=
  ∀ N n m : ℕ,m<N → ref 0 ≤ m →
  ∀ {I : Type} [Fintype I] [DecidableEq I] (B : Census I) (h : I → ℕ),
  Fintype.card I ≤ c → (∀ j,h j ≤ d) → (∀ j,ref (h j) ≤ m) →
  ∀ (_ : ∀ i : ℕ,LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n))) (v : voiceBall h G) (j : I),
  let F := (frames G).level (h j)
  ∃ (Y : Music F H N n) (Q : ∀ i,Coefficient F ((H).S.side i n)),
  ∀ i,m ≤ i → ∀ hi:i ≤ N,
    let Z := panorama (P:=P) h v.val j Y i
    let z := LocalLTE.Sail.sampleNorm H N (h j) i
    Account ((H).rep N n i) (hol G) Z (stretch z (Q i)) (Real.sqrt (A.B.a.clock.forcedAllowance i)) (priceAt P p N n i) ∧
    (∀ U,(vista (P:=P) (N:=N) (n:=n) B h v.val i hi U).part (B.fire j) = Z.density 0 (localSection G (h j)) ((H).rep N n i) U) ∧
    (i<N → ‖z‖ * F.coeffSize (F.core ((Y.tone i).index ((Y.tone (i+1)).index.symm (Q (i+1)).x) - (Q i).x)) ≤
        1/2 * priceAt P p N n (i+1) + priceAt P p N n i)

variable (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n)
    {D₀ : Factor A} {a : ℕ → ℝ} {W : Bid.Worth} {l q M j K d₀ c ι p : ℕ} {κ e : ℝ}
    (crew : Bandage.Harmonics D₀ a W P l) {Hₓ : Spool.Heights}
    (orders : Spool.Terms D₀.shape κ (p+1) j l q M K e A.delay Hₓ)
    (span : East.stagnate q 500<l) (reach : ∀ i j,(D₀.target i j).halo=500)

theorem reclosed_frames_of_library (lib : Bandage.Harmonics.Library crew orders span reach ref fields p d₀ c ι) :
    FramesReclose P ref p d₀ c := by
  intro N n m hm h₀ I _ _ B h card cap fits paths v j F
  obtain ⟨Y,Q,sung,_entries,_tour,reads⟩ := (lib N n m hm h₀ I B h v.val paths card cap fits v.property).2.1 j
  refine ⟨Y,fun i=>Q i (v.val j) K,?_⟩
  intro i lo hi Z z
  have book := reads i lo hi
  refine ⟨exhibition_account _ _ _ _ _ _ _ _ _ _ _ book.full book.ball,book.story,?_⟩
  intro step
  have earns (t : ℕ) (ht : m≤t) (top : t≤N) :
      ‖LocalLTE.Sail.sampleNorm H N (h j) t‖ * F.coeffSize ((Y.tone t).index (v.val j)-(Q t (v.val j) K).x) ≤ priceAt P p N n t := by
    have booked := (reads t ht top).ball.canon
    change F.coeffSize (LocalLTE.Sail.sampleNorm H N (h j) t • ((Y.tone t).plays (v.val j)).x -
      LocalLTE.Sail.sampleNorm H N (h j) t • (Q t (v.val j) K).x) ≤ _ at booked
    rw [←smul_sub,Size.smul,(sung.earned t ((fits j).trans ht) top).currents] at booked
    exact booked
  exact forecast_transport H W (Y.tone (i+1)) (Y.tone i) (localSection G (h j))
    (sung.earned _ (((fits j).trans lo).trans i.le_succ) step) (sung.earned _ ((fits j).trans lo) hi)
    (sung.step _ ((fits j).trans lo) step) crew.tag.clock.bank (v.val j) _ _
    (earns (i+1) (lo.trans i.le_succ) step) (earns i lo hi)

theorem purchased_physical_reclosure (G : Gauge) (simple : G.Simple) (p d c order : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (P : Bolt A)
      (ref : ℕ → ℕ) (fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n),
    let C := YM.Family.mk (Issue.trail P) (hol G) (frames G) (localSection G) ref fields
    Spec.Calibrated C ∧ C.Makes ∧ (∀ i,order ≤ (A.B.a.budget i).order) ∧
      ReclosedLibrary P ref fields p d c ∧ FramesReclose P ref p d c := by
  obtain ⟨X,D,A,R,M,Ra,p₀,μ,σ,F,F',W,Z,P,T,der,_pen,_bar,_post,_views,_fame,_timed,
    ref,fields,cal,ok,_bound,Hs,K,l,q,e,Γ,_port,_stately,a,_lower,_broad,hX,hQ,hr,_eld,
    AX,hM,orders,scales,z,hP,_survey,KX,Fx,hY,_scope,_repository,ι,_pack,_lane,lib⟩ :=
    PhysicalNext.Repeat.Legato.engineProducts simple p order d 1 1 c 1 0 0 0 (1/4)
      (κ:=1) zero_lt_one le_rfl le_rfl (by norm_num) 1
  exact ⟨X,D,A,P,ref,fields,cal,ok,der,reclosed_of_library P ref fields Γ hY hX hQ lib ok,
    reclosed_frames_of_library P ref fields Γ hY hX hQ lib⟩

end YM.Integration.FVA1Physical.Marked.Quay
