import YM.LocalLTE.Brochure.Company
import YM.LocalLTE.Georges.MarcoT
/-! Genuine selected Bolts, capacities all m.  Does not choose this Bolt using another production! Exposes more options via liftsB. -/
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
lemma springM (Ψ:Mallow.Prereq G) (m TT r:ℕ)(hp₀:LocalLTE.Fan.Pastel.chip (m+1)+1 < -(↑(r+1):ℝ)/2) {κ:ℝ}(hκ:0<κ)(U:Orders)(hU:ThroughLaunch.Draft U) (b₀:ℝ)(Θ:ℕ→ℕ→ℕ) (ζ:ℝ)(he:0<ζ) (σ:ℝ)(hσ:(↑(r+1):ℝ)/2<σ)(ht:ζ<(m:ℝ)/100): ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A),A.B.a.clock.kernel.penalty=κ∧ b₀≤A.B.a.clock.bar∧WithStage X.p U ∧ Mallow.Outlook r m A.delay ∧ (∃ f K, Nonempty (Bandage R f K)) ∧ MintZ A.delay σ r ∧ ∃ p0:ℕ,∃(F:Mallow.Funding R p0 1)(M:Mallow.Preview F)(W:Trail F m)(_V:Cready F W)(_D:Adorn F W),∃ P:Bolt A, Mallow.Made F W M P∧ Ψ.jobs A.delay F.κ ∧ Mallow.Merchandise R.shape W.footprint W.ψ A.delay ∧ ∃ Z:Mallow.Wickets R.target m ζ,Mallow.Bouquets R.shape Z F.κ Θ TT A.delay:=by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G κ hκ
  obtain ⟨p0,hv,⟨Wt⟩,hx⟩:= Mallow.sailing m (1/2) (by norm_num) r
  obtain ⟨s,T,C,K,hs,hV,hC⟩:= Legato.tripT hG Ψ U hU hp p0 TT m (show (1/2:ℝ)<1 by norm_num) Wt (hx _) (fun _=>1) Θ ζ he ht
  let u:Tariffs:=⟨fun _=>0,fun _=>le_rfl,fun _=>1⟩; let X:Extra.Multi.Scope:=⟨fun _=>1,fun _=>0,fun _=>1,fun _=>le_rfl,fun _=>Nat.zero_lt_one⟩
  obtain ⟨v,hv,H⟩:=hC u X; obtain ⟨⟨P⟩,hc⟩:= H v le_rfl; obtain ⟨w,hw⟩:=hc P
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩; let Y : Extra.Multi.Tariff:=⟨1,0,fun _=>le_rfl⟩
  obtain ⟨F,h⟩:= hw w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=>E) Y
  obtain ⟨θ,-,h⟩:= h _ (fun _=>one_pos)
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  obtain ⟨V,hV',hO,hT⟩:= h Q J ⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨U₁,hu₁,H₁⟩:= Mallow.forecast r m hp₀ V
  obtain ⟨U₂,hu₂,H₂⟩:= Mallow.pocketsZ r σ hσ U₁
  obtain ⟨b,hb'⟩:= Bar.exists_above U₂ b₀
  let I:Wait b:=⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩; obtain ⟨a,ha,hD⟩:=Wait.engine I hG
  obtain ⟨hP,B,hA,hS,R,-,-,-,-,-,hx0,-,-,-,⟨X',W,P',H',hK'⟩,hF⟩:= hT U₂ (hu₁.trans hu₂) b I _ ha hD
  obtain ⟨M⟩:= Mallow.previews X'; obtain ⟨T,hT⟩:= Mallow.emerging X' W H' M P' hG
  refine ⟨_,_,_,R,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hs)).trans hb, ?_, ⟨hV.first,hV.jets,hV.powers,hV.prices⟩,(H₁ _ hu₂),⟨_,_,hx0⟩,(H₂ _ (DelayLe.refl _)),p0,X',M,W,H',P',T,hT,hK'⟩
  change b₀≤ B.a.clock.bar; exact hb'.trans_eq B.valid.bar.symm


-- caller in same Bolt. Tour+reader.Analytic.Standard.Ph.M
open YM.LocalLTE.Port Mallow.Coterie
variable (p n Mζ Ra b CB MB :ℕ)(J' μ ζ σ:ℝ)(hJ:0≤J')(hx:0≤μ)(hp:(↑(p+1:ℕ):ℝ)/2<σ)(ht:(countB μ Mζ+2)*CB+(-ζ)≤-σ)(hv:ζ<(Ra:ℝ)/4)
variable (r:ℕ→ℕ→ℕ)(hr:∀ i j:ℕ,StepStages i j→Ra≤ r i j+1)
variable (U:Orders)(hU: ThroughLaunch.Draft U)(B':ℝ){κ:ℝ}(hκ:0<κ)(M:ℕ)(hk:ζ<(M:ℝ)/100)(hw:LocalLTE.Fan.Pastel.chip (M+1)+1 < - (↑(p+1:ℕ):ℝ)/2)
include hr hv hw hκ hU hk hp ht hx hJ
lemma fundedM : ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A),A.B.a.clock.kernel.penalty=κ∧ B' ≤ A.B.a.clock.bar ∧ WithStage X.p U∧ Mallow.Outlook p M A.delay ∧ (∃ f K, Nonempty (Bandage R f K)) ∧ MintZ A.delay σ p ∧ ∃ p0:ℕ, ∃ (F:Mallow.Funding R p0 1)(M':Mallow.Preview F)(W:Mallow.Trail F M),∃ (Z:Mallow.Wickets R.target M ζ)(P : Bolt A) (T:Circuit Mζ CB p M r F W M' μ ζ σ Z P), Mallow.Posters b MB CB J' μ ζ F.κ Ra A.delay∧ Views T b MB Ra J' :=by
   have h:0<ζ:=by have hF:0 < (↑(p+1):ℝ):=Nat.cast_pos.mpr (Nat.zero_lt_succ p); have h:0 ≤ (countB μ Mζ+2)*(CB:ℝ):=(by unfold countB; positivity); linarith only [h,ht,hp,hF]
   let V:= Mallow.valence G b MB CB J' μ ζ Ra hJ hx h hv
   let J':= Coterie.campJ G CB Mζ μ ζ hx h.le V -- `G` order.C
   obtain ⟨X,D,A,R,hΓ,hK0,hC,hO,hϵ,h₀,t,F,M',W,U,H,P,hM,⟨hV,hW⟩,hJ',Z,hK⟩:= Legato.springM hG J' M Mζ p hw hκ U hU B' r ζ h σ hp hk -- argument order.
   have he:∀ N m n,∀ h:m<N, Nonempty (Peer F W M' P p N m n h):=by
        intro N m n hp; obtain ⟨s,a,Q,G',k,k',x,hx',hG',hQ,hY⟩:= hM.held N m n hp; have he:Peg F G' W M' k' p hp (P.history N n (m+1)) (P.history N n m) x k:= hQ.symm ▸ hY.symm ▸ Mallow.pegged F G' W M' k' p hO hp H hG' x hx' hG
        exact ⟨⟨s,a,Q,G',k',x,k,he⟩⟩
   let T:Circuit Mζ CB p M r F W M' μ ζ σ Z P:= ⟨hK,hW,H,U,hJ',hM,h₀,ht,hx,fun N m n h=> (he N m n h).some⟩
   exact ⟨X,D,A,R,hΓ,hK0,hC,hO,hϵ,h₀,t,F,M',W,Z,P,T,hV,Coterie.amusement T b MB Ra _ hr hV hG⟩ -- Y.E shadow.
-- scope Endpoint in LTE. Additional projection pass.
omit hr hv hw hU hk hp ht
include n
theorem soldM : ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A) (M Ra p0:ℕ)(μ' σ:ℝ)(F:Mallow.Funding R p0 1)(M':Mallow.Preview F)(W:Mallow.Trail F M)(Z:Mallow.Wickets R.target M μ')(P:Bolt A) (T:Circuit Mζ CB p M (fun _ _=>Ra) F W M' μ μ' σ Z P), (∀ j,n≤ (A.B.a.budget j).order) ∧ A.B.a.clock.kernel.penalty=κ ∧ B' ≤ A.B.a.clock.bar ∧ Mallow.Posters b MB CB J' μ μ' F.κ Ra A.delay∧ Views T b MB Ra J' ∧ ∃ (r0:ℕ→ℕ) (Y:∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail P) N p), let C:= Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 Y ; Spec.Calibrated C ∧ C.Makes ∧ ∃ (hp:Bandage.Dynamo R P) (b:ℕ→ℝ) (K:Bid.Worth) (_:Bandage R b K)(G0:∀ N p m, m<N→ YM.MergeProof.GaugeDoor ((Issue.trail P).rep N p (m+1)) ((Issue.trail P).rep N p m)), (∀ N m n,∀ h:m<N, Bandage.ClimbsT R P N m n (G0 N n m h))∧∀ d N n, r0 d≤N → Bandage.FreightT P hp N n d (Y d N n) (r0 d) K (G0 N n) :=by
  let v: ThroughLaunch.Orders:= ⟨4,fun i=>6+n+i,fun i=>2+n+i,fun i=>100+(n:ℝ)+(i:ℝ)⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:=by change (100:ℝ)≤100+n+i; have hh:0≤ (n:ℝ):=(by positivity); have he:0≤(i:ℝ):=(by positivity); linarith only [he,hh]
  have hv: ThroughLaunch.Draft v:= ⟨le_rfl,fun i j h=>Nat.add_le_add_left h _,fun i j h=>Nat.add_le_add_left h _, (by intro i j hi; change (100:ℝ)+n+i≤ 100+n+j; gcongr),fun i=> (show (0:ℝ)<100 by norm_num).trans_le (hE _),fun i=>by change _≤6+n+i; omega,fun i=>by change _≤2+n+i; omega⟩
  let ζ:= (↑(p+1):ℝ)+(countB μ Mζ+2)*CB
  let σ:= (↑(p+1):ℝ); have h₁:(p:ℝ)≥0:=by positivity
  obtain ⟨M,hM⟩:= exists_nat_gt (100*ζ+100*(↑(p+1):ℝ)); obtain ⟨Ra,hR⟩:= exists_nat_gt (4*ζ)
  have hw:100*ζ < M:=by apply lt_trans _ hM; push_cast; linarith only [h₁]
  have he:0≤ζ:=by unfold ζ countB; positivity
  have hx' : LocalLTE.Fan.Pastel.chip (M+1)+1 < - (↑(p+1:ℕ):ℝ)/2:=by unfold LocalLTE.Fan.Pastel.chip; linarith only [show (↑(M+1):ℝ)=M+1 from by norm_cast, hM,he, show (↑(p+1):ℝ)≥1 from by push_cast; linarith only [h₁] ]
  obtain ⟨X,D,A,R,hB,hY,hC,hO,hϵ,h₀,p0,F,M',W,Z,P,T,hM,V⟩:= Legato.fundedM hG p Mζ Ra b CB MB J' μ ζ σ hJ hx (by unfold σ; push_cast; linarith only [h₁]) (by unfold σ ζ; linarith only) (by linarith only [hR]) (fun _ _=> Ra) (fun i j _=> Nat.le_succ _) v hv B' hκ M (by linarith only [hw]) hx'
  obtain ⟨b1,W0,⟨b0⟩⟩:= hϵ
  choose t ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
  let X1:Ranch R p0 M 1:= ⟨F,W,T.ground,T.cash,T.merch,M'⟩
  have he : Bandage.Dynamo R P:=by
       have he(N n m hp):= Mallow.savedZ F W P hG M' T.made T.ground T.cash (m:=m) (n:=n) (N:=N) hp
       refine ⟨fun i j=> he i j i le_rfl,fun N m n ht=> he N n m ht,fun N m j hm=>?_⟩
       let Sp:= T.fortune N m j hm; let U:Turf R N m j:= ⟨p0,M,1,X1,Sp.day,Sp.pass,Sp.bay,Sp.career,Sp.sign,Sp.dir,Sp.honor,Sp.deed.entry,fun _=> Sp.deed.film⟩
       exact ⟨U,Sp.leadOut.symm,Sp.leadIn⟩
  obtain ⟨D0,P',hP,hV,hZ,hE⟩:= Bandage.squadT hG b0 P he t ht
  refine ⟨X,D,A,R, M,Ra,p0,ζ,σ,F,M',W,Z,P,T,fun i=>?_,hB,hY,hM,V,t,P',hV,hP,he,b1,W0,b0,D0,hZ,hE⟩
  change n≤ (A.B.a.params i).order; rw [params_eq A.B.valid i,hC.jets]; change n≤6+n+A.B.a.clock.J i; omega
end YM.PhysicalNext.Repeat.Legato
