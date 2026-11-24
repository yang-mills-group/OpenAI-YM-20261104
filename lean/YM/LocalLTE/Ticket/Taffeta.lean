import YM.LocalLTE.Ticket.Woven
import YM.LocalLTE.MarkPT.Spring
import YM.LocalLTE.Ballot.Boat
import YM.LocalLTE.Weave.Producer
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
variable (p n d Mζ b CB MB:ℕ)(J' μ B' η:ℝ){κ :ℝ}(hκ:0<κ)(hJ:0≤J')(hx:0≤ μ)(hz:0<η)
include hκ hJ hx hz
/-! `s` is REAL visible inset coupling. precision per payer includes loss η arbitrarily small, inside norm at actual budgets. Public map ahead of slot fitting, consuming Φ.
-/
theorem engineColumn (TT:ℕ) : ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A) (M Ra p0:ℕ)(μ' σ:ℝ)(F:Mallow.Funding R p0 1)(M':Mallow.Preview F)(W:Mallow.Trail F M)(Z:Mallow.Wickets R.target M μ')(P:Bolt A) (T:Circuit Mζ CB p M (fun _ _=>Ra) F W M' μ μ' σ Z P), (∀ j,n≤ (A.B.a.budget j).order) ∧ A.B.a.clock.kernel.penalty=κ ∧ B' ≤ A.B.a.clock.bar ∧ Mallow.Posters b MB CB J' μ μ' F.κ Ra A.delay∧ Views T b MB Ra J' ∧ (∃ b0,Fame d b0 MB CB μ μ' F.κ Ra A.delay ∧ People T b0 d MB Ra) ∧ Coterie.TimedPT T ((↑(p+1):ℝ)-η) (penumbra η) (Scene.trackPower M) (richPT CB Mζ μ) ∧ ∃ (r0:ℕ→ℕ) (Y:∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail P) N p), let C:= Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 Y ; Spec.Calibrated C ∧ C.Makes ∧  (∀ d,d+3≤(Issue.trail P).levels.clock.J (r0 d)) ∧ ∃ (Hp:ℕ → ℝ)(K:Bid.Worth)(l q:ℕ)(e:ℝ)(Γ:Bandage.Harmonics R Hp K P l), Γ.port=(fun N m n h=> Legato.padT T N m n h)∧ (∀ d N n,r0 d≤N → Bandage.Stately Γ d N n (Y d N n) (r0 d))∧ (∃ a:ℕ,p≤ a ∧ Astonish Γ q a e ∧∃ (hX:East.stagnate q 500<l) (hQ:∀ i j,(R.target i j).halo=500)(hr:Spiral.Series R.shape M F.κ q l a p TT e A.delay), ∀ d N n:ℕ, r0 d ≤ N → ∃ P₀ : Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n, Extra.Histories.Sung (localSection G d) (Issue.trail P) N n (hol G) K (r0 d) P₀ ∧ (Y d N n).entries=(P₀.draft (Issue.trail P)).inits ∧∀ m:ℕ,r0 d ≤ m→ m ≤ N→ N-m ≤ TT+1→ ∀ X0: (i:ℕ)→LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n)), ∃ (f:∀ i:ℕ, ((Labels.frames G).level d).Coeff → YM.Source.Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side i n)), Bandage.Harmonics.Gala Γ hr hX hQ d P₀ f X0 m)  :=by
   let U:= (Coterie.burden CB Mζ μ); let Zx:= richPT CB Mζ μ; let ν:= penumbra η; have hxZ: U < (Zx:ℝ)/2:=by unfold Zx richPT; linarith only [Nat.lt_floor_add_one (2*(burden CB Mζ μ)), show (↑(Nat.floor (2*U)+1):ℝ)=Nat.floor (2*U)+1 from by push_cast; rfl] -- test rfl
   have hT:0 <ν:= lt_min (by positivity) (by norm_num); have hgV: (penumbra η) < ((↑(p+1):ℝ)-((↑(p+1):ℝ)-η))/2:=by unfold penumbra; linarith only [min_le_left (η/4) (1/4:ℝ),hz] -- unfold
   have hu: (penumbra η)<1/2:= lt_of_le_of_lt (min_le_right ..) (by norm_num : (1/4:ℝ)<1/2)
   let F0 (m:ℕ)(ν:ℝ)(Ra:ℕ): Involve G m Mζ ν (fun _ _=>Ra) := readersQ p m Mζ Zx ((↑(p+1):ℝ)-η) (penumbra η) (Coterie.burden CB Mζ μ) (Nat.le_refl _) hT hgV hxZ hu hG ν (fun _ _=>Ra)
   let v: ThroughLaunch.Orders:= ⟨4,fun i=>6+n+i,fun i=>2+n+i,fun i=>100+(n:ℝ)+(i:ℝ)⟩
   have hE (i:ℕ): 100 ≤ v.supportExp i:=by change (100:ℝ)≤100+n+i; have hh:0≤ (n:ℝ):=(by positivity); have he:0≤(i:ℝ):=(by positivity); linarith only [he,hh]
   have hv: ThroughLaunch.Draft v:= ⟨le_rfl,fun i j h=>Nat.add_le_add_left h _,fun i j h=>Nat.add_le_add_left h _, (by intro i j hi; change (100:ℝ)+n+i≤ 100+n+j; gcongr),fun i=> (show (0:ℝ)<100 by norm_num).trans_le (hE _),fun i=>by change _≤6+n+i; omega,fun i=>by change _≤2+n+i; omega⟩
   let ζ:= (↑(p+1):ℝ)+(countB μ Mζ+2)*CB
   let σ:= (↑(p+1):ℝ); have h₁:(p:ℝ)≥0:=by positivity
   let r:= 8+4*(p+TT); let η0:=4+(r:ℝ); have hp:p≤r:=by unfold r; omega
   have hs : -((r:ℝ)+1)/2 ≤ Spiral.grantZ p TT 0:=by unfold Spiral.grantZ r; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) TT,h₁]
   have heY : 2-η0 ≤ Spiral.grantZ p TT 0:=by unfold η0; linarith only [hs, Nat.cast_nonneg (α:=ℝ) r]
   have hVx:0 < η0:= by unfold η0; positivity
   have hη:1-η0 < -(↑(r+1):ℝ)/2:=by unfold η0; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) r]
   have hxζ:0≤ζ:=by unfold ζ countB; positivity
   obtain ⟨M,hM⟩:= exists_nat_gt (100*(ζ+η0)+100*(↑(p+1):ℝ)); obtain ⟨Ra,hR⟩:= exists_nat_gt (4*ζ)
   have hw:100*ζ < M:=by apply lt_trans _ hM; linarith only [hVx, show (0:ℝ)≤(p+1:ℕ) from by positivity]
   have he:0≤ζ:=by unfold ζ countB; positivity
   have hx' : LocalLTE.Fan.Pastel.chip (M+1)+1 < - (↑(p+1:ℕ):ℝ)/2:=by unfold LocalLTE.Fan.Pastel.chip; linarith only [show (↑(M+1):ℝ)=M+1 from by norm_cast, hM,he,hVx, show (↑(p+1):ℝ)≥1 from by push_cast; linarith only [h₁] ]
   obtain ⟨q,hq⟩:= exists_nat_gt (η0/(3/8))
   let lH:= East.stagnate q 500+1
   have hxR: η0< (3/8:ℝ)*q:= by linarith only [hq]
   let Hm: Elixir G M:= Spiral.loco (G:=G) M TT hVx hη (by linarith only [hM,hxζ, show (0:ℝ)≤(p+1:ℕ) from by positivity]) hxR (show _ < lH from Nat.lt_succ_self _) hs heY
   obtain ⟨X,D,A,R,hB,hY,hC,hO,hϵ,h₀,p0,F,M',W,Z,P,T,hM,V,V1,V2,V3⟩:= Legato.fundedGenevaC hG p d Mζ Ra b CB MB J' μ ζ σ hJ hx (by unfold σ; push_cast; linarith only [h₁]) (by unfold σ ζ; linarith only) (by linarith only [hR]) (fun _ _=> Ra) (fun i j _=> Nat.le_succ _) v hv B' hκ M (by linarith only [hw]) hx' (F0 M ζ Ra) lH Hm
   obtain ⟨b1,W0,⟨b0⟩,hEK,hQA⟩:= hϵ
   choose t ht' using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   have heV : Spiral.Series R.shape M F.κ q lH r p TT η0 A.delay:= V3
   let Λ:= Legato.slopeX hG T b0 hEK -- order?
   have hPui:= Legato.showsP (U:=Λ) (Bandage.Harmonics.earlier heV) hQA (show East.stagnate q 500< lH from Nat.lt_succ_self _) hG (fun _ _ _ _=>⟨rfl,rfl⟩)
   obtain ⟨Xf,ht0,hT',hg'⟩:= Bandage.stipples hG Λ t ht' -- exact mounts
   refine ⟨X,D,A,R,M,Ra,p0,ζ,σ,F,M',W,Z,P,T,fun i=>?_,hB,hY,hM,V,V1, (Coterie.playBill T _ _ _ Zx (Nat.le_refl _) hT hgV hxZ hu hG V2),t,Xf,hT',ht0,ht',b1,W0,lH,q,η0,Λ,rfl,hg',r,hp,hPui,Nat.lt_succ_self _,hQA,heV,?_⟩
   · change n≤ (A.B.a.params i).order; rw [params_eq A.B.valid i,hC.jets]; change n≤6+n+A.B.a.clock.J i; omega
   intro i N n hx; exact Bandage.Harmonics.current Λ hG heV (fun N m n hm=> ⟨rfl,rfl⟩) _ hQA i (Xf i N n) (t i) (hg' i N n hx) (ht' i)
end YM.PhysicalNext.Repeat.Legato
