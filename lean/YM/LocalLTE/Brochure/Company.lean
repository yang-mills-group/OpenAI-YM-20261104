import YM.LocalLTE.Brochure.Parade
/-! Genuine selected Bolts, capacities all m. No marked estimates yet. Does not choose this Bolt using another production! Exposes more options via liftsB. -/
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
-- caller in same Bolt. Tour+reader.Analytic.Standard.Ph.M
open YM.LocalLTE.Port Mallow.Coterie
variable (p n Mζ Ra b CB MB :ℕ)(J' μ ζ σ:ℝ)(hJ:0≤J')(hx:0≤μ)(hp:(↑(p+1:ℕ):ℝ)/2<σ)(ht:(countB μ Mζ+2)*CB+(-ζ)≤-σ)(hv:ζ<(Ra:ℝ)/4)
variable (r:ℕ→ℕ→ℕ)(hr:∀ i j:ℕ,StepStages i j→Ra≤ r i j+1)
variable (U:Orders)(hU: ThroughLaunch.Draft U)(B':ℝ){κ:ℝ}(hκ:0<κ)(M:ℕ)(hk:ζ<(M:ℝ)/100)(hw:LocalLTE.Fan.Pastel.chip (M+1)+1 < - (↑(p+1:ℕ):ℝ)/2)
include hr hv hw hκ hU hk hp ht hx hJ
lemma fundedT : ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A),A.B.a.clock.kernel.penalty=κ∧ B' ≤ A.B.a.clock.bar ∧ WithStage X.p U∧ Mallow.Outlook p M A.delay ∧ MintZ A.delay σ p ∧ ∃ p0:ℕ, ∃ (F:Mallow.Funding R p0 1)(M':Mallow.Preview F)(W:Mallow.Trail F M),∃ (Z:Mallow.Wickets R.target M ζ)(P : Bolt A) (T:Circuit Mζ CB p M r F W M' μ ζ σ Z P), Mallow.Posters b MB CB J' μ ζ F.κ Ra A.delay∧ Views T b MB Ra J' :=by
   have h:0<ζ:=by have hF:0 < (↑(p+1):ℝ):=Nat.cast_pos.mpr (Nat.zero_lt_succ p); have h:0 ≤ (countB μ Mζ+2)*(CB:ℝ):=(by unfold countB; positivity); linarith only [h,ht,hp,hF]
   let V:= Mallow.valence G b MB CB J' μ ζ Ra hJ hx h hv
   let J':= Coterie.campJ G CB Mζ μ ζ hx h.le V -- `G` order.C
   obtain ⟨X,D,A,R,hΓ,hK0,hC,hO,h₀,t,F,M',W,U,H,P,hM,⟨hV,hW⟩,hJ',Z,hK⟩:= Legato.volantT hG J' M Mζ p hw hκ U hU B' r ζ h σ hp hk -- argument order.
   have he:∀ N m n,∀ h:m<N, Nonempty (Peer F W M' P p N m n h):=by
        intro N m n hp; obtain ⟨s,a,Q,G',k,k',x,hx',hG',hQ,hY⟩:= hM.held N m n hp; have he:Peg F G' W M' k' p hp (P.history N n (m+1)) (P.history N n m) x k:= hQ.symm ▸ hY.symm ▸ Mallow.pegged F G' W M' k' p hO hp H hG' x hx' hG
        exact ⟨⟨s,a,Q,G',k',x,k,he⟩⟩
   let T:Circuit Mζ CB p M r F W M' μ ζ σ Z P:= ⟨hK,hW,H,U,hJ',hM,h₀,ht,hx,fun N m n h=> (he N m n h).some⟩
   exact ⟨X,D,A,R,hΓ,hK0,hC,hO,h₀,t,F,M',W,Z,P,T,hV,Coterie.amusement T b MB Ra _ hr hV hG⟩ -- Y.E shadow.
-- scope Endpoint in LTE. Additional projection pass.
omit hr hv hw hU hk hp ht
include n
theorem soldT : ∃ (X:Metals G)(D:Rolls X.p)(A:Alloy X D)(R:Factor A) (M Ra p0:ℕ)(μ' σ:ℝ)(F:Mallow.Funding R p0 1)(M':Mallow.Preview F)(W:Mallow.Trail F M)(Z:Mallow.Wickets R.target M μ')(P:Bolt A) (T:Circuit Mζ CB p M (fun _ _=>Ra) F W M' μ μ' σ Z P), (∀ j,n≤ (A.B.a.budget j).order) ∧ A.B.a.clock.kernel.penalty=κ ∧ B' ≤ A.B.a.clock.bar ∧ Mallow.Posters b MB CB J' μ μ' F.κ Ra A.delay∧ Views T b MB Ra J':=by
  let v: ThroughLaunch.Orders:= ⟨4,fun i=>6+n+i,fun i=>2+n+i,fun i=>100+(n:ℝ)+(i:ℝ)⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:=by change (100:ℝ)≤100+n+i; have hh:0≤ (n:ℝ):=(by positivity); have he:0≤(i:ℝ):=(by positivity); linarith only [he,hh]
  have hv: ThroughLaunch.Draft v:= ⟨le_rfl,fun i j h=>Nat.add_le_add_left h _,fun i j h=>Nat.add_le_add_left h _, (by intro i j hi; change (100:ℝ)+n+i≤ 100+n+j; gcongr),fun i=> (show (0:ℝ)<100 by norm_num).trans_le (hE _),fun i=>by change _≤6+n+i; omega,fun i=>by change _≤2+n+i; omega⟩
  let ζ:= (↑(p+1):ℝ)+(countB μ Mζ+2)*CB
  let σ:= (↑(p+1):ℝ); have h₁:(p:ℝ)≥0:=by positivity
  obtain ⟨M,hM⟩:= exists_nat_gt (100*ζ+100*(↑(p+1):ℝ)); obtain ⟨Ra,hR⟩:= exists_nat_gt (4*ζ)
  have hw:100*ζ < M:=by apply lt_trans _ hM; push_cast; linarith only [h₁]
  have he:0≤ζ:=by unfold ζ countB; positivity
  have hx' : LocalLTE.Fan.Pastel.chip (M+1)+1 < - (↑(p+1:ℕ):ℝ)/2:=by unfold LocalLTE.Fan.Pastel.chip; linarith only [show (↑(M+1):ℝ)=M+1 from by norm_cast, hM,he, show (↑(p+1):ℝ)≥1 from by push_cast; linarith only [h₁] ]
  obtain ⟨X,D,A,R,hB,hY,hC,hO,h₀,p0,F,M',W,Z,P,T,hM,V⟩:= Legato.fundedT hG p Mζ Ra b CB MB J' μ ζ σ hJ hx (by unfold σ; push_cast; linarith only [h₁]) (by unfold σ ζ; linarith only) (by linarith only [hR]) (fun _ _=> Ra) (fun i j _=> Nat.le_succ _) v hv B' hκ M (by linarith only [hw]) hx'
  refine ⟨X,D,A,R, M,Ra,p0,ζ,σ,F,M',W,Z,P,T,fun i=>?_,hB,hY,hM,V⟩
  change n≤ (A.B.a.params i).order; rw [params_eq A.B.valid i,hC.jets]; change n≤6+n+A.B.a.clock.J i; omega
end YM.PhysicalNext.Repeat.Legato
