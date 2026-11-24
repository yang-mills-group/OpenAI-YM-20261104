import YM.SignedWilsonExpansion.F9.EvaluateQ
import YM.SignedWilsonExpansion.F9.Naive
import YM.SignedWilsonExpansion.Purchase.China
/-!
# Commission benchmark permit porter. Pruning budget.Escala. Every issued Porch must have coherence with these same numerical dials and Cover.Time. Left lifts filtration.Scope.W.
-/
set_option autoImplicit false
set_option maxHeartbeats 590000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense Ticket Cosmos Cosmos.Polestar
open Source
open MarqueQ Method PorchK
open scoped Topology Classical BigOperators
variable {G:Gauge} {M: Levels G}{e n l c m b r v h d k u K:ℕ} {x:Fin n→ Cover}{T:Initialize G} {R:Realm G (e+1) Credit.leanC}{H:Hol G}{F:Labels.Frames G}{Ω:Council F}
open WardBin
variable (p₁:∀ i,(Ω i).Sound H)(p₂:∀ i,Bid.pop (Ω i)) (P:Install (e:=e) (G:=G) H (⟨F.level,Ω,p₁,p₂⟩:Master H) R K)
variable (Q:∀ h,Rays G h T.hol)(V:u ≤ K)(hy:k+e≤K)(ha:h ≤ k)(hz:Ample h u (k+e))
lemma heightAge (p:Ample h u (k+e))(v:d≤h): Ample d u (k+e):= ⟨le_trans (by omega) p.all,le_trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ v)) p.ranks, le_trans (Nat.mul_le_mul v v) p.floor⟩
lemma advanceCan {X Y:ℝ}(v: Canopy R m l X)(p:X≤Y): Canopy R m l Y:=⟨v.arch,v.order, ⟨fun i u p'=> ( v.pad.year _ u p' ).trans p,v.pad.lengthS.trans p⟩, v.span.trans p⟩
include p₁ p₂ P V hy ha hz
lemma covers : ∃ U: WilsonCoeffUV.Bank.Credit,∀ (v:ℝ),1≤v → ∀ (m c:ℕ),R.anchor ≤ m → m ≤ c → PadRank R m c v → v≤ U.buy v ∧ Stair Ω (launch F T.hol T.surveys Q k) R.draws R.paid m c c h e k u ( U.buy v ):=by
    let L':= unitedBill T.hol F T.surveys Q h k e u ha; obtain ⟨B,hB,hW⟩:=L'; let T':Credit:=⟨0,B,hB⟩; let L(i:Fin (h+1)):= cover (G:=G) (⟨F.level,Ω,p₁,p₂⟩:Master H) i.val k e u K ((Nat.le_of_lt_succ i.isLt).trans ha) V hy ( heightAge hz ( Nat.le_of_lt_succ i.isLt ) ); let s (i):= (L i).choose
    obtain ⟨W,hW'⟩:= Shard.uniformPays (P:=fun i V=>∀ x:ℝ,1≤x→ (s i).buy x≤Credit.buy V x) Finset.univ (fun i _=>⟨s i,fun _ _=> le_rfl⟩) (fun i _ _ _ v p x z=>(p x z).trans (v x z))
    let A:Credit:= T'.plus W; let D:=Credit.leanC.plus A; refine ⟨ D, fun x hv m c hw ht hp=>?_ ⟩
    have z: Credit.buy A x ≤ D.buy x:= Credit.thickened Credit.leanC hv; exact ⟨(Credit.lean_cost ..).symm.trans_le ( Credit.thickens A hv ), fun d v=> climbs ( ( L ⟨d,Nat.lt_succ_of_le v⟩ ).choose_spec x hv R P m c c hw ht le_rfl hp ) ((( hW' _ ( Finset.mem_univ _) x hv ).trans ( Credit.thickened T' hv )).trans z),hW ( D.buy x ) (( (show B=T'.buy x by simp [Credit.buy,T']).trans_le ( Credit.thickens W hv ) ).trans z)⟩
variable {ι:Type}{ρ B U Y P_:ι→ℝ}{L:Filter ι}
include V hy
variable {c l m b r v:ι→ℕ}(w: Rise B L)(p_: ∀ i,0<ρ i ) (vU:∀ᶠ i in L,l i ≤ m i ∧ m i≤ b i ∧ b i≤ v i ∧ v i≤ c i ∧ l i≤r i∧ r i≤v i)
abbrev coherentQ (x:PorchK T F Q Ω R h k u)(i:ι)(m₀ b₀ v₀ c₀ r₀ l₀:ι→ℕ)(p:∀ i,0<ρ i) (B:ι→ℝ): Prop:= x.m=m₀ i∧ x.b=b₀ i∧ x.v=v₀ i∧ x.c=c₀ i∧ x.r=r₀ i∧ x.l=l₀ i ∧ x.ρ=ρ i∧ x.Z=B i∧ x.mesh = roof R.draws (l₀ i) (c₀ i) (ρ i) (p i)
structure Yonder (R:Realm G (e+1) Credit.leanC)(L:Filter ι)(m b v c r l:ι→ℕ)(Z:ι→ℝ) (p:∀ i,0<ρ i)(q:ι→ PorchK T F Q Ω R h k u)(B:ι→ℝ): Prop where
     frame : ∀ᶠ i in L, coherentQ Q (q i) i m b v c r l p Z
     badge : Wage L (Spread B) 1 Z
     horizon : (hereD R.draws ρ m)⁻¹ ≤ᶠ[L] Z
include w vU
lemma invitation [L.NeBot] (X:∀ᶠ i in L, Canopy R (l i) (c i) (U i)) (p: Wage L (Spread B) 1 U)(z: hereD R.draws ρ v ≤ᶠ[L] (1:ι→ℝ)) (grant: Wage L (Spread B) 1 ( (hereD R.draws ρ m)⁻¹ )) : ∃ (ξ:ι→ℝ)(Q':ι→ PorchK T F Q Ω R h k u),Yonder (G:=G) (Ω:=Ω) Q R L m b v c r l ξ p_ Q' B:=by
    obtain ⟨C,t⟩:= covers p₁ p₂ P Q V hy ha hz; let A(i):=hereD R.draws ρ m i; let ζ:= A⁻¹+U; let X':=fun i=> C.buy (ζ i)
    have hh:∀ᶠ i in L,∃ y: PorchK T F Q Ω R h k u, coherentQ Q y i m b v c r l p_ X'∧ ( A i )⁻¹ ≤ X' i:=by
        filter_upwards [X,z,vU] with i hL hi ⟨a,b',hk,ht,hl,h₁⟩; have hw:0<A i:= sizeT_pos _ (p_ i) _; have hz: U i ≤ ζ i:= le_add_of_nonneg_left ( inv_nonneg.mpr hw.le ); let hP:= advanceCan hL hz; have hc:m i ≤ c i:= by omega
        have hv:= hL.cut a hc le_rfl; obtain ⟨t₀,hq⟩:= t (ζ i) hP.positive ( m i ) (c i) hv.arch hc ( advanceCan hv hz ).pad; refine ⟨{m:=m i,c:=c i,l:=l i,mesh:= roof R.draws ( l i ) (c i) (ρ i) (p_ i),ρ:=ρ i,Z:=X' i,paid:=hq,align:=rfl,b:=b i,v:=v i,r:=r i,berth:=b',desk:=hk,endo:=ht,cost:=advanceCan hP t₀,dat:=a,datum:=hl,landing:=h₁,pos:=p_ i, small:= hi}, ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩, le_trans (le_add_of_nonneg_right (zero_le_one.trans hL.positive)) t₀⟩ -- mesh specify
    haveI : Nonempty ( PorchK T F Q Ω R h k u ):= let ⟨i,z,h⟩:=hh.exists; ⟨z⟩
    let f(i:ι): PorchK T F Q Ω R h k u:= if h:(∃ Q': PorchK T F Q Ω R h k u, coherentQ Q Q' i m b v c r l p_ X') then h.choose else Classical.arbitrary _
    refine ⟨X',f,hh.mono (fun i ⟨p,h,h'⟩=>by unfold f; let z:= ( show ∃ y, coherentQ Q y i m b v c r l p_ X' from ⟨p,h⟩ ); rw [dif_pos z]; exact z.choose_spec), Wage.ornament C _ ( Wage.plus (( y_rise w ).eventually_ge_atTop 1) grant p ), hh.mono fun i ⟨q,h,v⟩=> v ⟩
-- eventual gate.Frame extends cuts. No fix cut order hacks.
omit p₁ p₂ P V hy ha hz w vU
variable (Z:ι→ PorchK T F Q Ω R h k u) {z:ℝ}
lemma Yonder.spectrum (H:Yonder Q R L m b v c r l U p_ Z B) : ∀ᶠ i in L, l i≤ m i∧ m i≤ b i∧ b i≤ v i∧ v i≤ c i∧ l i≤ r i ∧ r i≤ v i :=H.frame.mono fun i ⟨a,g,t,v,h',s,o,p,hz⟩=>by rw [←s,←a,←g,←t,←v,←h']; exact ⟨(Z i).dat,(Z i).berth,(Z i).desk,(Z i).endo,(Z i).datum,(Z i).landing⟩
def balcony (U:WilsonCoeffUV.Bank.Credit)(V:ι→ℝ)(i:ι): ℝ:= max ((U.plus Credit.leanC).buy (V i)) (1:ℝ)
lemma wageC (h:Maxer L Y)(p:Wage L Y (1:ι→ℝ) B): Billed L Y B:=by
    obtain ⟨d,h'⟩:=p; obtain ⟨C,z,hz⟩:= h'.exists_pos; let U:Credit:= ⟨d,max C 1,le_max_right ..⟩; refine ⟨U,?_⟩; filter_upwards [h,hz.bound] with i hi hv ; let H:= pow_nonneg (zero_le_one.trans hi) d; rw [Pi.one_apply,mul_one,Real.norm_of_nonneg H] at hv; exact hv.trans (mul_le_mul_of_nonneg_right (le_max_left ..) H)
include w
lemma Yonder.invest (p:Yonder Q R L m b v c r l U p_ Z B) : ∃ C:Credit,let f:= balcony C (Spread B); Maxer L f ∧ (∀ᶠ i in L,(Z i).Z≤ f i) ∧ Wage L (Spread B) 1 f ∧ Spread B=O[L] f:=by
   have hx:= ( y_rise w ).eventually_ge_atTop 1; obtain ⟨C,hv⟩:= (wageC hx p.badge); refine ⟨C,?_⟩; intro f; let S:= Spread B; let N:= C.plus Credit.leanC; have hk:Maxer L f:= Eventually.of_forall fun i=> le_max_right ..; refine ⟨hk,?_ ,?_ ,?_⟩
   · filter_upwards [hv,hx,p.frame] with i hi hx' ⟨_,_,_,_,_,_,_,hv,hH⟩; exact hv.trans_le (((le_abs_self (U i)).trans hi).trans ((Credit.thickens _ hx').trans (le_max_left ..)))
   · refine Wage.fix (Wage.ornament N _ (wageSpread (L:=L) (B:=B))) (hx.mono fun i hi=>(max_eq_left (N.purchase hi)).symm) (.refl ..)
   refine IsBigO.of_norm_eventuallyLE (hx.mono fun i hi=>?_); change ‖ Spread B i‖ ≤ _; rw [Real.norm_of_nonneg (zero_le_one.trans hi)]; exact ( Credit.lean_cost _ ).symm.trans_le (( Credit.thickened _ hi ).trans (le_max_left ..))
lemma chargeC (p: Wage L (Spread B) 1 Y): Y=O[L] dollar B:= polyLeM w p
lemma Yonly (p: Wage L (Spread B) 1 Y)(n:ℕ): Tendsto (fun i=> Y i^n * cent B i) L (𝓝 0):=by
    refine Wage.next_zero (Wage.fix (Wage.mul ( Wage.power p n ) ( Wage.enroll (u:=Spread B) (isBigO_refl (cent B) L) )) (.refl ..) (?_)) (daybreak w); exact Eventually.of_forall fun i=>by change 1^n*cent B i= _; rw [one_pow,one_mul]
local notation "S₀"=> (fun i=>roof R.draws (l i) (c i) (ρ i) (p_ i))
lemma Canon (p:Yonder Q R L m b v c r l U p_ Z B)(he:Stretched L S₀)(vY:Wage L (Spread B) 1 Y)(hY:∀ᶠ i in L,(Z i).Z≤ Y i)(hz:0<z)(h: hereD R.draws ρ v ≤ᶠ[L] payD B ( -z )): FrontQ Z L Y (mark B) (dollar B) (cent B):=by
   let u(i):= sizeT R.draws (ρ i) (v i); have hv:(fun i=>(Z i).markW)=ᶠ[L] u:= p.frame.mono fun i ⟨a,b,hi,_,_,_,hk,_⟩=>by dsimp only[markW,πMark]; rw [hk,hi]
   let f:= fun i=> (Z i).mesh; have he': S₀=ᶠ[L] f:= p.frame.mono fun i h=> h.2.2.2.2.2.2.2.2.symm; have hp₀: Maxer L Y:= hY.mono fun i hi=>((Z i).cost.positive).trans hi; refine ⟨⟨hp₀,Wage.rel (p:=fun i=>(Z i).Z) (show Wage L Y 1 Y from ⟨1,by simp; exact isBigO_refl _ _⟩) (IsBigO.of_norm_eventuallyLE (hY.mono (fun i h=>by change ‖(Z i).Z‖ ≤ _; rw [ Real.norm_of_nonneg ( zero_le_one.trans (Z i).cost.positive )]; exact h ))) ⟩,(?_),polyLeM w vY,( M_rise w ).eventually_ge_atTop 1,(?_ ),mark_sold w,Yonly w vY⟩
   · exact ⟨he.endpt.congr' (he'.fun_comp Mesh.spacing), fun k=> (he.pay k).congr' (he'.mono fun i hi=>by change S₀ i =f i at hi; dsimp only [Expense.a,sides,nodes]; change (S₀ i).spacing^k * ((S₀ i).p.side.val:ℝ)= _; rw [hi])⟩
   intro n; exact (((isBigO_refl ( (dollar B)^n ) L).mul ( Consume.ordered (A:=u) (Eventually.of_forall fun i=> ( sizeT_pos _ (p_ i) _ ).le) h )).trans_tendsto ( dollar_op w z hz n ) ).congr' ( hv.symm.mono fun i hi=>by dsimp only [Pi.mul_apply,Pi.pow_apply]; rw [show markW (Z i)= u i from hi.symm])
end YM.SignedWilsonExpansion.Purchases.HalfRoof.Minty
