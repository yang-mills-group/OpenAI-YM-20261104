import YM.LocalLTE.Orbit.Engine
import YM.LocalLTE.Quay.Paid
import YM.LocalLTE.Quay.Pre
import YM.LocalLTE.Keels.Spark
import YM.LocalLTE.Sail.Pinnacle
import YM.LocalLTE.XPane.Aerie
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow
variable {G:Gauge} (hG:G.Simple)
include hG
/-! Selected theories for EVERY prescribed finite order and derivative/source budget.
 No assertion coupling coherence as n,p/Mζ etc vary. One ACTUAL common construction C
 with below all properties per prescription. See YM.LocalLTE.LTE for ledger/scopes.
-/
open YM.LocalLTE.Port Mallow.Coterie YM.LocalLTE.Weft
variable (p n d Mζ b CB MB:ℕ)(J' μ B' η:ℝ){κ :ℝ}(hκ:0<κ)(hJ:0 ≤ J')(hx:0 ≤  μ)(hz:0<η)
include hκ hJ hx hz
/-! `s` is REAL visible inset coupling. precision per payer includes loss η arbitrarily small, inside norm at actual budgets. Public map ahead of slot fitting, consuming Φ.
-/
/-!
# Schedule demands after order

 No assertion simultaneity X/estimator/table as TT,p vary. Quantum LOCAL estimate.
 Includes SAME C17 capabilities, and stronger real-history windows on canonical marks
 with readout and evaluation. P0_L above desired p to leave p+1 after normalization etc.
-/
open Mallow Spiral
open Legato.Spool
set_option maxHeartbeats 840000 in
theorem engineProducts (TT:ℕ) : ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A) (M Ra p0:ℕ)(μ' σ:ℝ)(F:Mallow.Funding R p0 1)(M':Mallow.Preview F)(W:Mallow.Trail F M)(Z:Mallow.Wickets R.target M μ')(P:Bolt A) (T:Circuit Mζ CB p M (fun _ _=>Ra) F W M' μ μ' σ Z P), (∀ j,n≤ (A.B.a.budget j).order) ∧ A.B.a.clock.kernel.penalty=κ ∧ B' ≤ A.B.a.clock.bar ∧ Mallow.Posters b MB CB J' μ μ' F.κ Ra A.delay∧ Views T b MB Ra J' ∧ (∃ b0,Fame d b0 MB CB μ μ' F.κ Ra A.delay ∧ People T b0 d MB Ra) ∧ Coterie.TimedPT T ((↑(p+1):ℝ)-η) (penumbra η) (Scene.trackPower M) (richPT CB Mζ μ) ∧ ∃ (r0:ℕ→ℕ) (Y:∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail P) N p), let C:= Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 Y ; Spec.Calibrated C ∧ C.Makes ∧  (∀ d,d+3≤(Issue.trail P).levels.clock.J (r0 d)) ∧ ∃ (Hp:ℕ → ℝ)(K:Bid.Worth)(l q:ℕ)(e:ℝ)(Γ:Bandage.Harmonics R Hp K P l), Γ.port=(fun N m n h=> Legato.padT T N m n h)∧ (∀ d N n,r0 d≤N → Bandage.Stately Γ d N n (Y d N n) (r0 d))∧ (∃ a:ℕ,p≤ a ∧ Astonish Γ q a e ∧∃ (hX:East.stagnate q 500<l) (hQ:∀ i j,(R.target i j).halo=500)(hr:Spiral.Series R.shape M F.κ q l a (5*CB+p+1) TT e A.delay), (∀ d N n:ℕ, r0 d ≤ N → ∃ P₀ : Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n, Bandage.Harmonics.Eldorado Γ hr hX hQ d P₀ (Y d N n) (r0 d) CB p (5*(CB:ℝ)+(p:ℝ)+1)) ∧ ∃ (AX:Almanac)(hM:∀ N m n hm,(Γ.port N m n hm).ac=M ∧(Γ.port N m n hm).ranch.allocation.κ= F.κ)(X0:Chronicles R.shape M F.κ q l a (plot CB p TT) TT e A.delay AX)(g: ℕ→ Mallow.ConcertZ R.target M (plot CB p TT)) (z:GuideF) (hP:Mobility AX R.shape A.delay z g CB l TT F.κ), Survey Γ X0 hM hQ hX hP r0 Y (look CB p TT) p ∧ ∃ (KX:ℕ)(Fx:Spool.Heights) (hY:Spool.Terms R.shape F.κ (p+1) a l q M KX e A.delay Fx), Spool.Scope KX (p+1) A.delay∧ (∀ d N n:ℕ,r0 d ≤ N → Bandage.Harmonics.Repository Γ hY hX hQ d (Y d N n) (r0 d)) ∧∃ (ι₀:ℕ), Spool.Package R.shape F.κ (p+1) a l KX d CB ι₀ e A.delay ∧ Spool.LaneQ A.delay p (p+1) ∧ Bandage.Harmonics.Library Γ hY hX hQ r0 Y p d CB ι₀) :=by
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

   obtain ⟨X,D,A,R,hB,hY,hC,hO,hϵ,h₀,p0,F,M',W,Z,P,T,hM,V,V1,V2,V3⟩:= Legato.fundedGenevaC hG p d Mζ Ra b CB MB J' μ ζ σ hJ hx (by unfold σ; push_cast; linarith only [h₁]) (by unfold σ ζ; linarith only) (by linarith only [hR]) (fun _ _=> Ra) (fun i j _=> Nat.le_succ _) v hv B' hκ M (by linarith only [hw]) hx' (F0 M ζ Ra) lH X'
   obtain ⟨b1,W0,⟨b0⟩,hEK,hQA⟩:= hϵ
   choose t ht' using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   have heV : Spiral.Series R.shape M F.κ q lH r vH TT η0 A.delay:= And.left (And.left (And.left (And.left (And.left (And.left (And.left V3))))))
   have huP : Pinned (X:=X) R.shape F.κ A.delay M CB lH p vH TT φ:= And.right (And.left (And.left (And.left (And.left (And.left (And.left V3))))))
   let Λ:= Legato.slopeX hG T b0 hEK -- order?
   have hPui:= Legato.showsP (U:=Λ) (Bandage.Harmonics.earlier heV) hQA (show East.stagnate q 500< lH from Nat.lt_succ_self _) hG (fun _ _ _ _=>⟨rfl,rfl⟩)
   obtain ⟨Xf,ht0,hT',hg'⟩:= Bandage.stipples hG Λ t ht' -- exact mounts
   refine ⟨X,D,A,R,M,Ra,p0,ζ,σ,F,M',W,Z,P,T,fun i=>?_,hB,hY,hM,V,V1, (Coterie.playBill T _ _ _ Zx (Nat.le_refl _) hT hgV hxZ hu hG V2),t,Xf,hT',ht0,ht',b1,W0,lH,q,η0,Λ,rfl,hg',r,hp,hPui,Nat.lt_succ_self _,hQA,heV,?_,?_⟩
   · change n≤ (A.B.a.params i).order; rw [params_eq A.B.valid i,hC.jets]; change n≤6+n+A.B.a.clock.J i; omega
   · intro i N n hx; exact Bandage.Harmonics.associated Λ hG heV (fun N m n hm=> ⟨rfl,rfl⟩) _ hQA i (Xf i N n) (t i) (hg' i N n hx) (ht' i) CB p φ hΦ huP
   have hKx : Charge M CB πL T0 TT lH q r G z' η0 F.κ (X:=X) R.shape A.delay:= And.right (And.left (And.left (And.left (And.left (And.left V3)))))
   obtain ⟨hp,Qa,h,g,hX0,hY0⟩:= hKx -- actual order
   refine ⟨Qa,(fun _ _ _ _=>⟨rfl,rfl⟩),hX0,g,h,hY0,?_⟩
   refine ⟨?_,?_⟩
   · exact Legato.survey_present Λ hX0 hp (show Patronage CB πL p T0 TT z' A.delay from And.right (And.left (And.left (And.left (And.left V3))))) (fun _ _ _ _=> ⟨rfl,rfl⟩) hG hQA (Nat.lt_succ_self _) hΦ' hY0 t ht' Xf ht0 hg'
   have hScope : Spool.Scope K (p+1) A.delay:= (V3.1.1.2)
   have hx:Spool.Terms R.shape F.κ (p+1) r lH q M K η0 A.delay Ha:=V3.1.1.1.2
   have hP r N n (hr:t r≤ N): Bandage.Harmonics.Repository Λ hx (Nat.lt_succ_self _) hQA r (Xf r N n) (t r):= Λ.fillsY hG hx (fun _ _ _ _=>⟨rfl,rfl⟩) (Nat.lt_succ_self _) hQA hQ' r (Xf r N n) (t r) (hg' r N n hr) (ht' r)
   have hKp : Spool.Package R.shape F.κ (p+1) r lH K d CB i0 η0 A.delay:= V3.1.2; have hr':Spool.LaneQ A.delay p (p+1) :=V3.2
   exact ⟨K,Ha,hx,hScope,hP,i0,hKp,hr', Λ.admits hG hx (fun _ _ _ _=>⟨rfl,rfl⟩) (Nat.lt_succ_self _) hQA hQ' hKp t Xf ht0 hr' hvM (hP0.trans (Nat.le_succ _)) ht' hP hScope⟩
end YM.PhysicalNext.Repeat.Legato
