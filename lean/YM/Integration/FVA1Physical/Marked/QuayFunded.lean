import YM.Integration.FVA1Physical.Marked.QuayTensor
import YM.Integration.FVA1Physical.Round2.JointWindows

/-! Retain the complete native Quay library through `jointCircuit`, including
its exact positive-grade, mixed, and formal coefficient books. The preselection
and growth argument follows `Round2.QuayJoint.funded_library`. The original
proof discarded the library after extracting a scalar readout. Its analytic
choices here also serve the caller's extra parameter agenda and the Docket. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Round2
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow
open YM.LocalLTE.Port Mallow.Coterie YM.LocalLTE.Weft Mallow Spiral Legato.Spool
open YM.Qlocal.Schedule
open YM.Integration.FVA1Physical.Round2.Quay
open YM.Integration.FVA1Physical.Marked.Quay

/-- The original physical stem, inventory and terminal library retained with the
orders and port proofs needed by new consumers. -/
structure PhysicalBooks {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (R : Factor A) (P : Bolt A)
    (ref : ℕ → ℕ) (fields : ∀ d N n,TransferData ((Labels.frames G).level d) (Issue.trail P) N n) (p d c : ℕ) where
  rates : ℕ → ℝ
  worth : Bid.Worth
  l : ℕ
  q : ℕ
  M : ℕ
  r : ℕ
  K : ℕ
  ι : ℕ
  κ : ℝ
  cost : ℝ
  height : Spool.Heights
  crew : Bandage.Harmonics R rates worth P l
  orders : Spool.Terms R.shape κ (p+1) r l q M K cost A.delay height
  span : East.stagnate q 500<l
  reach : ∀ i j,(R.target i j).halo=500
  registered : Bandage.Harmonics.Library crew orders span reach ref fields p d c ι

theorem PhysicalBooks.reclosed {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {R : Factor A} {P : Bolt A}
    {ref : ℕ → ℕ} {fields : ∀ d N n,TransferData ((Labels.frames G).level d) (Issue.trail P) N n} {p d c : ℕ}
    (b : PhysicalBooks R P ref fields p d c)
    (ok : Family.Makes (Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) ref fields)) :
    ReclosedLibrary P ref fields p d c ∧ FramesReclose P ref p d c ∧ UniformTensor P ref p d c :=
  ⟨reclosed_of_library P ref fields b.crew b.orders b.span b.reach b.registered ok,
    reclosed_frames_of_library P ref fields b.crew b.orders b.span b.reach b.registered,
    tensor_of_library P ref fields b.crew b.orders b.span b.reach b.registered ok⟩

variable {G : Gauge} (hG : G.Simple) {goal : Goal G} (finance : Obtainable goal)
variable (p n d Mζ b CB MB:ℕ)(J' μ B' η:ℝ){κ:ℝ}(hκ:0<κ)(hJ:0≤J')(hx:0≤μ)(hz:0<η)
include hG finance hκ hJ hx hz Mζ b MB B'
set_option maxHeartbeats 2100000 in
theorem funded_books (TT:ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (R : Factor A) (P : Bolt A)
      (color : G.ColorIndex)
      (r₀ : ℕ→ℕ) (Y : ∀ d N m,TransferData ((Labels.frames G).level d) (Issue.trail P) N m),
      let C := Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r₀ Y
      goal X D A R ∧ Extension.UV.Archive A.B ∧ OPE.Therm.Poetry C.path.levels ∧
      Spec.Calibrated C ∧ C.Makes ∧ (∀ j,n≤(A.B.a.budget j).order) ∧
      Docket C color X.O A.B.M A.B.kin ∧ A.B.a.clock.kernel.penalty=κ ∧ Nonempty (PhysicalBooks R P r₀ Y p d CB) := by
   let U:= (Coterie.burden CB Mζ μ); let Zx:= richPT CB Mζ μ; let ν:= penumbra η; have hxZ: U < (Zx:ℝ)/2:=by unfold Zx richPT; linarith only [Nat.lt_floor_add_one (2*(burden CB Mζ μ)), show (↑(Nat.floor (2*U)+1):ℝ)=Nat.floor (2*U)+1 from by push_cast; rfl] -- test rfl
   have hT:0 <ν:= lt_min (by positivity) (by norm_num); have hgV: (penumbra η) < ((↑(p+1):ℝ)-((↑(p+1):ℝ)-η))/2:=by unfold penumbra; linarith only [min_le_left (η/4) (1/4:ℝ),hz] -- unfold
   have hu: (penumbra η)<1/2:= lt_of_le_of_lt (min_le_right ..) (by norm_num : (1/4:ℝ)<1/2)
   let F0 (m:ℕ)(ν:ℝ)(Ra:ℕ): Involve G m Mζ ν (fun _ _=>Ra) := readersQ p m Mζ Zx ((↑(p+1):ℝ)-η) (penumbra η) (Coterie.burden CB Mζ μ) (Nat.le_refl _) hT hgV hxZ hu hG ν (fun _ _=>Ra)
   let v: ThroughLaunch.Orders:= ⟨4,fun i=>6+n+i,fun i=>2+n+i,fun i=>100+(n:ℝ)+(i:ℝ)⟩
   have hE (i:ℕ): 100 ≤ v.supportExp i:=by change (100:ℝ)≤100+n+i; have hh:0 ≤  (n:ℝ):=(by positivity); have he:0 ≤ (i:ℝ):=(by positivity); linarith only [he,hh]
   have hv: ThroughLaunch.Draft v:= ⟨le_rfl,fun i j h=>Nat.add_le_add_left h _,fun i j h=>Nat.add_le_add_left h _, (by intro i j hi; change (100:ℝ)+n+i≤ 100+n+j; gcongr),fun i=> (show (0:ℝ)<100 by norm_num).trans_le (hE _),fun i=>by change _≤6+n+i; omega,fun i=>by change _≤2+n+i; omega⟩
   let ζ:= (↑(p+1):ℝ)+(countB μ Mζ+2)*CB
   let σ:= (↑(p+1):ℝ); have h₁:(p:ℝ)≥0:=by positivity
   let vH:ℕ:= 5*CB+p+1; let φ:ℝ:=5*(CB:ℝ)+(p:ℝ)+1; have hpH:p≤vH:=by unfold vH;omega
   have heV : φ=(vH:ℝ):=by unfold φ vH; norm_cast
   have h':0 ≤  (vH:ℝ):=Nat.cast_nonneg _; have hΦ:0<φ:=by unfold φ;positivity
   let πL:= look CB p TT; let T0:= plot CB p TT; let z' :ℝ:= (T0:ℝ)
   have hxκ:vH ≤ T0:=by unfold vH T0 plot look; nlinarith -- look unfolds? 
   have hΦ' :0<z':=by unfold z' T0 plot; positivity
   have hS : T0≥ πL:= by unfold T0 πL plot; omega
   have hΨ:chronicleShift TT*(CB:ℝ)<((πL:ℝ)-p)/2:=by unfold chronicleShift πL look; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) TT,Nat.cast_nonneg (α:=ℝ) CB,mul_nonneg (Nat.cast_nonneg (α:=ℝ) CB) (Nat.cast_nonneg (α:=ℝ) TT)]
   have he'ζ:chronicleShift TT*CB+ -z'< -((πL:ℝ)+1)/2:=by unfold z' T0 plot πL look chronicleShift; push_cast; nlinarith only [h₁,Nat.cast_nonneg (α:=ℝ) TT,Nat.cast_nonneg (α:=ℝ) CB,mul_nonneg (Nat.cast_nonneg (α:=ℝ) CB) (Nat.cast_nonneg (α:=ℝ) TT)]
   have hTκ: grantZ T0 TT 0 ≤ grantZ vH TT 0:=by unfold grantZ; gcongr
   let r:= 32+4*(T0+TT); let η0:=4+(r:ℝ); have hp:p≤r:=by unfold r; omega
   have hxV :φ ≤ η0:=by have h : (vH:ℝ) ≤ r:= Nat.cast_le.mpr (by unfold r;omega); unfold η0; linarith only [heV,h]
   have hs : -((r:ℝ)+1)/2 ≤ Spiral.grantZ T0 TT 0:=by unfold Spiral.grantZ r; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) TT,Nat.cast_nonneg (α:=ℝ) T0]
   have heY : 2-η0 ≤ Spiral.grantZ T0 TT 0:=by unfold η0; linarith only [hs, Nat.cast_nonneg (α:=ℝ) r]
   have hVx:0 < η0:= by unfold η0; positivity
   have hη:1-η0 < -(↑(r+1):ℝ)/2:=by unfold η0; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) r]
   have hxζ:0 ≤ ζ:=by unfold ζ countB; positivity
   obtain ⟨M,hM⟩:= exists_nat_gt (100*(ζ+η0)+100*(↑(p+1):ℝ)); obtain ⟨Ra,hR⟩:= exists_nat_gt (4*ζ)
   have hw:100*ζ < M:=by apply lt_trans _ hM; linarith only [hVx, show (0:ℝ)≤(p+1:ℕ) from by positivity]
   have he:0 ≤ ζ:=by unfold ζ countB; positivity
   have hx' : LocalLTE.Fan.Pastel.chip (M+1)+1 < - (↑(p+1:ℕ):ℝ)/2:=by unfold LocalLTE.Fan.Pastel.chip; linarith only [show (↑(M+1):ℝ)=M+1 from by norm_cast, hM,he,hVx, show (↑(p+1):ℝ)≥1 from by push_cast; linarith only [h₁] ]
   obtain ⟨q,hq⟩:= exists_nat_gt (η0/(3/8))
   let lH:= East.stagnate q 500+1
   have hxR: η0< (3/8:ℝ)*q:= by linarith only [hq]
   have hγ:η0<M/100:=by linarith only [hM,hxζ, show (0:ℝ)≤(p+1:ℕ) from by positivity]
   let Hx: Elixir G M:= Spiral.loco (G:=G) M TT hVx hη hγ hxR (show _ < lH from Nat.lt_succ_self _) (hs.trans hTκ) (heY.trans hTκ)
   let Hm: Elixir G M:= thresholdX M CB lH p vH TT φ hΦ (by unfold Spiral.grantZ; push_cast; linarith only [heV, h', Nat.cast_nonneg (α:=ℝ) TT]) (by unfold φ; linarith only [Nat.cast_nonneg (α:=ℝ) CB,h₁]) (hxV.trans_lt hγ) Hx 
   have hs': z' ≤ η0:=by have h: (T0:ℝ)≤ (r:ℝ):=Nat.cast_le.mpr (by unfold r;omega); unfold z' η0; linarith only [h]
   let S':= Spiral.campaign G M CB πL (show z' ≤ (T0:ℝ) from le_rfl) he'ζ hS hΦ' hs' hη hγ hxR (show _ < lH from Nat.lt_succ_self _) hs heY Hm
   have hRk: grantZ T0 TT 0 < -((πL:ℝ)+1)/2:= lt_of_lt_of_le (slant T0 TT 0 (Nat.zero_le _)) (by gcongr) -- underscores
   have hζL : -z' < -((πL:ℝ)+1)/2:=by unfold z'; linarith only [show (πL:ℝ)≤ T0 from Nat.cast_le.mpr hS,show (1:ℝ)<T0 from by exact_mod_cast (show 1<T0 from (by unfold T0 plot look; omega))] -- edit
   let Sp : Elixir G M:= Spiral.hinter G CB M πL p T0 TT z' hζL hRk hΨ S'
   let K:=128*(p+5)
   obtain ⟨i0,hi0⟩:= exists_nat_gt (4*((LocalLTE.Vault.most G d:ℝ)*CB- echoBit K+2))
   have hxM:(LocalLTE.Vault.most G d:ℝ)*CB- 1/4*(i0:ℝ)< echoBit K-1:=by linarith only [hi0]
   have hvM:1≤ i0:=by
       apply Nat.one_le_iff_ne_zero.mpr; intro h; rw [h,Nat.cast_zero,mul_zero] at hxM; linarith only [hxM, bitN K, show 0 ≤ (LocalLTE.Vault.most G d:ℝ)*CB from by positivity ]
   obtain ⟨Ha,hHa,hP0⟩:= Spool.jewel_height M η0 q i0
   have hy: Spool.echoBit K < -(↑(p+1+1):ℝ)/2:=by unfold echoBit K; push_cast; linarith only [h₁]
   have hInterest: -((r:ℝ)+1)/2 < echoBit K:=by
       unfold echoBit K r; have hT : (T0:ℝ)≥p:= Nat.cast_le.mpr (show p≤T0 from hpH.trans hxκ); push_cast; linarith only [h₁,hT,Nat.cast_nonneg (α:=ℝ) TT]
   have hCap:2-η0 < echoBit K:=by unfold η0; linarith only [hInterest,Nat.cast_nonneg (α:=ℝ) r]
   have hQ': 1 ≤ q:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hf=> (by rw [hf,Nat.cast_zero,mul_zero] at hxR; linarith only [hxR,hVx]))
   let B0: Elixir G M:= Spool.gainJ M q K η0 r lH (p+1) Ha hHa (Nat.lt_succ_self _) hQ' hInterest hCap hy hη hγ hxR G Sp -- order
   let p1:= p+1; let X0:= reflected p1 K M G hy B0
   have hbη: echoBit K< -((p1+2:ℕ):ℝ):=by unfold echoBit K p1; push_cast; linarith only
   let X1:= Spool.meters G M lH p1 r K CB d i0 η0 hbη hInterest hCap hG hxM X0
   let X':= Spool.furtherQ M p p1 G (Nat.lt_add_one _) X1

   haveI := hG.nontrivial_color
   have degree : 0<G.lieDim := by rw [Gauge.lieDim,← G.colorIso.finrank_eq]; exact Module.finrank_pos
   let color : G.ColorIndex := ⟨0,degree⟩
   obtain ⟨voice,clear⟩ := YM.MSbar.Heath.vocals G
   let purpose := (finance.also (coarseRoom_obtainable (G:=G))).also
     (YM.Qlocal.Schedule.vacuumInvoice_obtainable hG color voice clear)
   obtain ⟨X,D,A,R,grant,archive,hB,hY,hC,hO,hϵ,h₀,p0,F,M',W,Z,P,T,hM,V,V1,V2,paid⟩:= jointCircuit hG purpose p d Mζ Ra b CB MB J' μ ζ σ hJ hx (by unfold σ; push_cast; linarith only [h₁]) (by unfold σ ζ; linarith only) (by linarith only [hR]) (fun _ _=> Ra) (fun i j _=> Nat.le_succ _) v hv B' hκ M (by linarith only [hw]) hx' (F0 M ζ Ra) lH (withPoetry X')
   have V3 : Fulfilled X' F W := paid.1
   obtain ⟨b1,W0,⟨b0⟩,hEK,hQA⟩:= hϵ
   choose t ht' using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   have heV : Spiral.Series R.shape M F.κ q lH r vH TT η0 A.delay:= And.left (And.left (And.left (And.left (And.left (And.left (And.left V3))))))
   let Λ:= Legato.slopeX hG T b0 hEK -- order?
   obtain ⟨Xf,ht0,hT',hg'⟩:= Bandage.stipples hG Λ t ht' -- exact mounts
   have hScope : Spool.Scope K (p+1) A.delay:= (V3.1.1.2)
   have hx:Spool.Terms R.shape F.κ (p+1) r lH q M K η0 A.delay Ha:=V3.1.1.1.2
   have hP r N n (hr:t r≤ N): Bandage.Harmonics.Repository Λ hx (Nat.lt_succ_self _) hQA r (Xf r N n) (t r):= Λ.fillsY hG hx (fun _ _ _ _=>⟨rfl,rfl⟩) (Nat.lt_succ_self _) hQA hQ' r (Xf r N n) (t r) (hg' r N n hr) (ht' r)
   have hKp : Spool.Package R.shape F.κ (p+1) r lH K d CB i0 η0 A.delay:= V3.1.2; have hr':Spool.LaneQ A.delay p (p+1) :=V3.2

   have lib := Λ.admits hG hx (fun _ _ _ _=>⟨rfl,rfl⟩) (Nat.lt_succ_self _) hQA hQ' hKp
     t Xf ht0 hr' hvM (hP0.trans (Nat.le_succ _)) ht' hP hScope
   obtain ⟨⟨ideal,room⟩,vac⟩ := grant
   have growth : Tendsto (fun m=>(A.B.a.params m).order) atTop atTop := by
     apply tendsto_atTop.2
     intro i
     filter_upwards [eventually_ge_atTop (t i)] with m hm
     exact (Nat.le_succ i).trans (((ht0.stages i).2 m hm).1)
   have docket := circuit_docket Λ room voice hG vac.2.1 color t Xf (vac.1 growth)
   refine ⟨X,D,A,R,P,color,t,Xf,ideal,archive,?_,hT',ht0,?_,docket,hB,
     ⟨⟨_,_,lH,q,M,r,K,i0,F.κ,η0,Ha,Λ,hx,Nat.lt_succ_self _,hQA,lib⟩⟩⟩
   · exact paid.2 A.asks A.B.a A.B.valid
   · intro i
     change n≤(A.B.a.params i).order
     rw [params_eq A.B.valid i,hC.jets]
     change n≤6+n+A.B.a.clock.J i
     omega
end YM.PhysicalNext.Repeat.Legato.Round2
