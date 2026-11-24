import YM.SignedWilsonExpansion.F9.Board
import YM.WilsonCoeffUV.Product.Report.Pre
/-!
# Request price on the very same company window

Chooses without tests, origins, cutoffs, periods. Post constants can use the
rolled lengths. Parameter `D` is arbitrary finite numeric horizon, permits
requesting all the needed ports at once. Lower rank uses *post* bill;
projection/contraction bill is in `floorL` only.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} (Ñ:ChartRatio G)(K:KernelChoices)(j:ℕ){A:Levels G}{h p k m N u e i l r:ℕ}{F:Labels.Frame G h}{H:Hol G}
def preboundSize (H:Hol G)(F:Frame G h)(t:Ample h u r)(v s:ℝ)(hp:0<s):= backL (h+1)*peak H F u r t v s hp*coinL (h+1)
lemma clearance (H:Hol G)(F:Frame G h)(t: Ample h u r): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → (A.S.block m).val=L → ∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2), roomV A m v ∧∀ (u:craftQuest A m j v)(x:roomV A m v), clear H F t (liftWing Ñ w u x):=by
    have hw i: ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J (m+1)=j → (A.S.block m).val=L → A.clock.J m=i → ∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2)(u:craftQuest A m j v)(x:roomV A m v), clear H F t (liftWing Ñ w u x):=by
       by_cases p: 4≤ i ∧ 5≤ j; swap; · exact Eventually.of_forall fun L A m _ z _ hc v _ _ _=> False.elim (p ⟨hc ▸ A.clock.adm m,z ▸ v⟩)
       obtain ⟨i0,j0⟩:= p; let s:= saffron G K i j i0 j0
       let c:= preboundSize H F t (knotV G K i j i0 j0) s (safron_nn G K i j i0 j0)
       filter_upwards [logLane c] with L h; intro A m a b g o v w q x; subst K j L i; unfold clear prebound; unfold c preboundSize at h; exact h
    have hp:= Polestar.preSpaced F H Ñ K (Nat.lt_succ_self _) 0 j
    filter_upwards [hp,(eventually_all_finset (Finset.range (j+1))).mpr (fun i _=>hw i)] with L hL r; intro A m p v x y z; exact ⟨(hL A m p v x y z).1,r (A.clock.J m) (Finset.mem_range.mpr (Nat.lt_succ_of_le ((A.fits.mono m.le_succ).trans v.le))) A m p v x rfl y z⟩

lemma closure_bill (L:Side)(H:Hol G)(F:Frame G h)(k e:ℕ)(t: Ample h u r): ∀ᶠ V:ℝ in atTop,∀ (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J (m+1)=j → A.S.block m=L → ∀ (v:5≤ A.clock.J (m+1))(w:h+1≤ A.clock.J (m+1)-2)(u:craftQuest A m j v)(x:roomV A m v), let I:=liftWing Ñ w u x; clear H F t I → Bill H F t I k e V:=by
    have hh a b: ∀ᶠ z:ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → A.clock.J m=a → A.clock.J (m+2)=b → A.S.block m=L →∀ (v:5≤ A.clock.J (m+1))(w:h+1≤A.clock.J (m+1)-2)(u:craftQuest A m j v)(x:roomV A m v), let I:=liftWing Ñ w u x; clear H F t I → Bill H F t I k e z:=by
       by_cases he:∃ (A:Levels G)(m:ℕ), A.clock.kernel=K ∧ A.clock.J (m+1)=j ∧ A.clock.J m=a∧ A.clock.J (m+2)=b∧ A.S.block m=L ∧∃ v:5≤A.clock.J (m+1), (h+1≤A.clock.J (m+1)-2) ∧ craftQuest A m j v ∧ roomV A m v
       · obtain ⟨A,m,hp,hh,ha,hb,x,v,t',u,V⟩:= he; subst K a j b L; let I:=liftWing Ñ t' u V; filter_upwards [eventually_ge_atTop (propel H F t I e),eventually_ge_atTop (render I k e _ r)] with y hy hz; intro B i g h L x b w z s k'; rw [←spike Ñ g L h x b t' z u s V k']; dsimp only; exact fun v=> ⟨v,hy,hz⟩
       dsimp only; exact Eventually.of_forall (fun c B i g h L x b w z s k _=>False.elim (he ⟨B,i,g,h,L,x,b,w,z,s,k⟩))
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr (fun a _=> (eventually_all_finset S).mpr fun b _=>hh a b)] with y h
    intro A m p q l v w u x; have he:A.clock.J m≤ A.clock.J (m+1):= A.fits.mono m.le_succ; have hx:A.clock.J (m+2)≤A.clock.J (m+1)+1:= A.fits.stepSlow (m+1); exact h _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m p q rfl rfl l v w u x
-- all relevant at a fixed stage j;
-- Defer state costs on x in ZZ at level before angular inputs.
def DemandL (H:Hol G)(F:Master H)(L:ℕ): Prop:= ∀ A:Levels G,∀ m:ℕ,A.clock.kernel=K→ A.clock.J (m+1)=j→ (A.S.block m).val=L → ∀ v:5≤ A.clock.J (m+1), roomV A m v ∧∀ h:ℕ,∀ w:h+1≤ A.clock.J (m+1)-2,∀ (u:craftQuest A m j v)(x:roomV A m v) (r a: Fin (j+1)) (S:Ample h a r), clear H (F.F h) S (liftWing Ñ w u x)
lemma seekL (H:Hol G)(F:Master H): ∀ᶠ L:ℕ in atTop,DemandL Ñ K j H F L:=by
    let I:=Fin (j+1); have hx (h r a:I) : ∀ᶠ L:ℕ in atTop,∀ (S: Ample h a r) (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → (A.S.block m).val=L → ∀ (v:5≤ A.clock.J (m+1))(w:h.val+1≤ A.clock.J (m+1)-2)(u:craftQuest A m j v)(x:roomV A m v),clear H (F.F h.val) S (liftWing Ñ w u x):=by
       by_cases v:Ample h a r; swap; · exact Eventually.of_forall fun _ g=>False.elim (v g)
       filter_upwards [clearance Ñ K j H (F.F h.val) v] with L hL; exact fun _ B i h v' z q f=> (hL B i h v' z q f).2
    filter_upwards [(eventually_all.mpr fun h=>eventually_all.mpr fun i=>eventually_all.mpr fun a=> hx h i a), Polestar.preSpaced (F.F 0) H Ñ K (Nat.lt_succ_self _) 0 j] with L hv hu
    intro A m v a u w; refine ⟨(hu A m v a u w (by omega)).1, fun h f t g r b S=>hv (⟨h,by omega⟩: I) r b S A m v a u w f t g⟩
def DemandZ (L:Side)(H:Hol G)(F:Master H)(z:ℝ):Prop:= ∀ A:Levels G,∀ m:ℕ,A.clock.kernel=K→ A.clock.J (m+1)=j→ A.S.block m=L → ∀ v:5≤ A.clock.J (m+1),∀ h:ℕ,∀ w:h+1≤ A.clock.J (m+1)-2,∀ (u:craftQuest A m j v)(x:roomV A m v)(r a:Fin (j+1)) (S:Ample h a r)(k e:Fin (j+1)), clear H (F.F h) S (liftWing Ñ w u x) → Bill H (F.F h) S (liftWing Ñ w u x) k e z
lemma seekZ (L:Side)(H:Hol G)(F:Master H): ∀ᶠ z:ℝ in atTop, DemandZ Ñ K j L H F z:=by
    let I:= Fin (j+1); have hx (h k e r a:I) : ∀ᶠ V:ℝ in atTop,∀ (S:Ample h a r) (A:Levels G)(m:ℕ), A.clock.kernel=K → A.clock.J (m+1)=j → A.S.block m=L → ∀ (v:5≤ A.clock.J (m+1))(w:h.val+1≤ A.clock.J (m+1)-2)(u:craftQuest A m j v)(x:roomV A m v), let I':=liftWing Ñ w u x; clear H (F.F h) S I' → Bill H (F.F h) S I' k e V:=by
       by_cases v:Ample h a r; swap; · exact Eventually.of_forall fun _ g=>False.elim (v g)
       filter_upwards [closure_bill Ñ K j L H (F.F h) k e v] with z h; exact fun _=> h
    filter_upwards [eventually_all.mpr fun h=> eventually_all.mpr fun k=> eventually_all.mpr fun e=>eventually_all.mpr fun r=>eventually_all.mpr fun a=>hx h k e r a] with z hz; intro A m v u x h t w g y r b s k e; exact hz (⟨t,by omega⟩:I) k e r b s A m v u x h w g y
-- stage requirements
variable {Ñ K j}
open Real
private abbrev LNeed (Ñ:ChartRatio G)(H:Hol G)(F:Master H)(K:KernelChoices)(j:ℕ): ℕ:= (eventually_atTop.mp (seekL Ñ K j H F)).choose
private abbrev ZNeed (Ñ:ChartRatio G)(H:Hol G)(F:Master H)(K:KernelChoices)(L:Side)(j:ℕ): ℝ:= exp (exp ((eventually_atTop.mp (seekZ Ñ K j L H F)).choose))
def pres (Ñ: ChartRatio G)(H:Hol G)(F:Master H)(K:KernelChoices) := floors G K id ⊔ (fun j=>LNeed Ñ H F K j) ⊔ fun j=>preMark Ñ K j j
def posts (Ñ: ChartRatio G)(H:Hol G)(F:Master H){P:Sheet G}(X:Rolls P) := Ticket.voucher X id Ñ ⊔ (fun j=> ZNeed Ñ H F P.kernel (X.L j) j) ⊔ fun j=> postMark Ñ P.kernel j j (X.L j)

-- `Install` rich only on requested numeric tiers; Regulator Q's later budgets enter before limits
structure Install (H:Hol G)(F:Master H)(R: Realm G (e+1) Credit.leanC)(D:ℕ): Prop where
    bed : ∀ k≤D,∀ u≤D,Dormitory R k u Credit.leanC
    lamp : ∀ k≤ D,∀ u≤D,∀ b≤ D,SpringD R k u b Credit.leanC
    aim : ∀ h≤D, ∀ m (v:R.anchor≤ m), ∃ I:Cloister G h, relight R.draws R.paid m (R.mint m v) I∧ ∀ a u r:Fin (D+1),∀ q:ℕ, q≤ e → ∀ S:Ample h u r,Bill H (F.F h) S I a q (R.cash Credit.leanC m)

variable {P:Sheet G}{X:Rolls P}{Ω: Protection X}{D:Delays Ω}{o:Bar D}{b:Supply.Wait o}{H:Hol G} {Z:Master H}
lemma realize (g:G.Simple)(q:LocalRatio Ñ)(a:Paid b A)(pre:pres Ñ H Z P.kernel≤ P.floorL)(post:posts Ñ H Z X≤ D.betaEntry)(e V:ℕ): ∀ᶠ m:ℕ in atTop,∃ R:Realm G (e+1) Credit.leanC,R.draws=A ∧ R.paid=Ñ ∧ R.y=zz A ∧ R.anchor=m ∧ Install H Z R V:=by
    have hx: Tendsto (fun i=> A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
    obtain ⟨W,Wage⟩:=eventually_atTop.mp (hx.eventually_ge_atTop (5+V+e)); refine (eventually_ge_atTop W).mono (fun m t=>?_)
    change W≤ m at t
    have hz (i) (u:m ≤ i): 5 ≤ A.clock.J (i+1)∧ V+3≤ A.clock.J (i+1)∧ e+1≤ A.clock.J (i+1):= by have H:= Wage i (t.trans u); omega
    have hL:= (sup_le_iff.mp (sup_le_iff.mp pre).1).1; have hβ: Ticket.voucher X id Ñ ≤ D.betaEntry:= (sup_le_iff.mp (sup_le_iff.mp post).1).1
    obtain ⟨i0,h₀,_⟩:= install_awards (Ñ:=Ñ) g q hL a hβ m (e+1) (fun j h=> ⟨(hz j h).1,(hz j h).2.2⟩)
    have hp (i) (p:m ≤ i): ∀ v:5≤ A.clock.J (i+1), craftQuest A i (A.clock.J (i+1)) v:= fun v=>afforded a.kernel a.lengths id hL i v
    have hy i : A.S.block i=X.L (A.clock.J (i+1)):=by rw [← A.fits.sameFactor,a.lengths]
    let Y i (p:m ≤ i):=quest A i Ñ (hz i p).1 (hp i p _); let V':=Credit.leanC; let R: Realm G (e+1) V' :={
       draws:=A
       paid:=Ñ
       hG:=g
       green:=q
       anchor:=m
       y:= zz A
       depth:=i0
       age:=h₀
       mint:=Y
       crossing:=fun _ _=> le_rfl
       taxes:=fun i p=> by
          let j:= A.clock.J (i+1); rw [Credit.lean_cost]; have hg:=hy i; have hi:= scriptVoucher X id Ñ j (le_trans (hβ j) ((booked g a hβ m).pays i p)); have hb:= (eventually_atTop.mp (deferred P.kernel (X.L j) j j Ñ)).choose_spec (zz A i) hi A i a.kernel rfl hg ((hz i p).1) (hp i p (hz i p).1); exact further hb (hz i p).2.2 le_rfl
       }
    have hr (i):R.cash Credit.leanC i= zz A i:= Credit.lean_cost (zz A i)
    have he k u d (h:k≤ V) (ho:u≤ V)(hU:d≤ V) (i:ℕ)(v:m≤ i): let I:=(Y i v).gear; DormP I k e u (R.cash Credit.leanC i)∧ poreF G e k u d I≤ R.cash Credit.leanC i:=by
       let j:=A.clock.J (i+1); have ⟨hV,hp0,he⟩:=hz i v; have hr: preMark Ñ P.kernel j j≤ (A.S.block i).val:= by rw [hy]; exact ((sup_le_iff.mp pre).2 j).trans (X.large j).need
       have hg: postMark Ñ P.kernel j j (A.S.block i) ≤ A.clock.hatBeta i:= by rw [hy]; exact ((sup_le_iff.mp post).2 j).trans (a.pays i)
       rw [show R.cash Credit.leanC i= zz A i from by exact Credit.lean_cost _]; exact handled Ñ P.kernel j j k u d e A i a.kernel rfl hV (hp _ v _) (by unfold j; omega) (by unfold j; omega) (by unfold j; omega) (by unfold j; omega) hr hg -- fix hp variable shadow
    refine ⟨R,rfl,rfl,rfl,rfl,⟨fun k e u g' j v=>(he k u 0 e g' (Nat.zero_le _) j v).1, fun k x u t b y=> ⟨fun i h=>(he k u b x t y i h).2⟩,?_⟩⟩; intro h p i L
    change m≤ i at L; let j:= A.clock.J (i+1); have hj' := hz i L
    have hP : LNeed Ñ H Z P.kernel j≤ (A.S.block i).val:= by rw [hy]; exact ((sup_le_iff.mp (sup_le_iff.mp pre).1).2 j).trans (X.large j).need
    have hg : ZNeed Ñ H Z P.kernel (A.S.block i) j ≤ A.clock.hatBeta i:= by rw [hy]; exact ((sup_le_iff.mp (sup_le_iff.mp post).1).2 j).trans (a.pays i)
    let x:=hj'.1; have v:h+1≤j-2:=by unfold j; omega
    obtain ⟨hs,hw⟩:= (eventually_atTop.mp (seekL Ñ P.kernel j H Z)).choose_spec _ hP A i a.kernel rfl rfl x
    let I:= liftWing Ñ v (hp i L _) hs; refine ⟨I,lamplight ..,fun ⟨a0,ha⟩ ⟨u,hu⟩ ⟨r,hr0⟩ q q' S=>?_⟩
    have hz:= embargo A hg
    rw [hr]
    exact (eventually_atTop.mp (seekZ Ñ P.kernel j (A.S.block i) H Z)).choose_spec _ hz A i a.kernel rfl rfl x h v (hp i L _) hs ⟨r,by unfold j; omega⟩ ⟨u,by unfold j; omega⟩ S ⟨a0,by unfold j; omega⟩ ⟨q,by unfold j; omega⟩ (hw h v (hp i L _) hs ⟨r,by unfold j; omega⟩ ⟨u,by unfold j; omega⟩ S)
end YM.WilsonCoeffUV.Mer.Xa
