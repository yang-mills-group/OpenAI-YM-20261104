import YM.Contacts.Junction.Mesa
/-! # auxiliary true post horizon commission. Uses designated teller knobs only.
 Inputs NOT claims about commune final at all periods yet.
 Ensures growth through stadium (theta arbitr after; no changing orientations).
 -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} (P: Patch) {O : ChartRatio G} {σ σ' C C' e v d t K τ ω' s a R:ℝ}{n k j r i q:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector Token
variable {U:Teller G} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U O X k P.L σ C M n}
variable {Q:ℝ→ℝ} {κ:KernelChoices}{β:Clip}{ξ:ℝ}
namespace Bookend
-- Participation harvest.Cash q need `Aux.Coat.manifest Sense+ chosenβ` produced at later.Charger. Pose for every healthy x might want from PrePlanner who budgets x; provide no universal bound assumes flag. Smaller c. Budget Brough. 
open Travel
variable (W:ConnectedActivityE6.Target G U)(B:ConnectedActivityE6.Target.Order G ξ)(A:Before G σ C P.J U.bind (n+3))
abbrev Office (G:Gauge)(U:Teller G)(O:ChartRatio G)(x:G.ColorIndex)(k:ℕ)(L:Side)(σ C:ℝ)(M:Uniform.ChartPrices)(n:ℕ):= StagePort G U O x k L σ C M n
variable (z:Office G U O X k P.L σ C M n)
def Seat (μ:ℝ) (x:z.dew.X):Prop := let f:=z.dew; let t:=z.pearlRide; ∃ a:ℝ, Nonempty (Cash ξ t μ P.L W B a f.T (Pane.virgin f.T z.budget f.β)) ∧ ∃ V:Coat f.T f.B,V.x=t∧V.width=B.K∧V.manifest∧flags (Pressure.temp t) V.V=∅∧ V.V=Cove.ship x
structure Rung (μ σ' C':ℝ)(y:ℕ)(Q:ℝ→ℝ) :Prop where -- define args below fix
    page : z.dew.S.patch=P
    binder : z.dew.S.kernel=U.bind
    scout : (Sienna.warm A page binder).Service z.dew.B z.dew.T.high z.dew.T.up z.dew.ρ
    agency : ClassicalMatch z.dew.B z.dew.T.high z.dew.T.low z.dew.T.up z.dew.T.down z.dew.ρ
    outdoor : ∃ Λ:ℝ,z.dew.T.down.Bounds z.dew.T.low σ' C' Λ
    depart : z.taxi=Q z.pearlRide
    zeroSeat : Seat P W B z μ 0
    highWard : ∃ i:BudgetPoint,i.threshold= Pressure.temp z.pearlRide
    ship : ∃ j, y≤j ∧ n+3≤ j∧ Up z j ((j+1:ℝ)⁻¹) j
    healthy : let x:= betaF G z.pearlRide P.L;∀ i j:ℕ,j+i<k+3→j≠0→ Pulse.Rooted (Range.cheap _) (z.outB (i+j-2) j) (x^(((y+1:ℝ))⁻¹))
-- rank j descriptor, Tills arr. Use monotonic y instance Stall can prove weaker by Budget.AtClock.
abbrev Buys (μ a:ℝ)(x:z.dew.X):Prop:=
    Seat P W B z μ x → ‖x‖+ 2*furl G P.L z.pearlRide < z.flag → 0<z.push x ∧ Brush (n+1) ((betaF G z.pearlRide P.L)^a) z.flag⁻¹ (Vita z) x

-- p.T.clip need Teller low, top. proven. Receipt chooses any. no O equality? Sienna O Q.table need score Arrival.C.Ph.Scheme.PT safety if O differs: Quiescent independent O. works!
variable (hm:0<R)(hk:2≤k)(hn:k ≤ n)(hQ:Bolt G P.L Q) (hg:G.Simple)(hO:LocalRatio O)
include W hm
-- h.G aux Arc quiescent any valid mount.
lemma lifting_budget (he:2 ≤ n) (J:BareRates.pre G σ' C' (n+3)) (E':FiberFee W.table ((n+3)+1))(hQ:Bolt G P.L Q) : ∃ (d:ℝ),0<d∧∀ y:ℝ,y<0→∀ᶠ t in atTop, ∀ z:StagePort G U O X k P.L σ C M n,t=z.pearlRide → ∀ v,Rung P W B A z R σ' C' v Q → ∀ x:z.dew.X, Seat P W B z R x → ‖x‖+2*furl G P.L t< z.flag → Loyalty z (furl G P.L t) (betaF G t P.L^y) d x:= by
    obtain ⟨d,hd,H⟩:= our_procure W B P A U.below.clip U.top.clip Q hQ E' J R hm (by omega); refine ⟨d,hd,fun s hs=>?_⟩; filter_upwards [H s hs,(YM.Work.E09.betaF_growth G P.L).eventually_ge_atTop 1] with t hx ht' z hT j h x hp hh; subst t;
    let D:=z.dew; let T:=D.T; let F:=D.B; let t:= z.pearlRide; let v:= furl G P.L t; let d':= betaF G t P.L; have ht:0< d':= zero_lt_one.trans_le ht'; have hv:0≤ v:= Real.rpow_nonneg ht.le _; obtain ⟨Λ,hl⟩:=h.outdoor; obtain ⟨B',hb⟩:=h.highWard
    obtain ⟨i,-,-,hP⟩:= h.ship; let hP' :=hP.truePE; have hT' : T.high=U.top.clip:=hP'.intake.ready.high; have hL : T.low= U.below.clip:= hP'.intake.ready.low; let f:=T.up;
    have he y (hS:Seat P W B z R y)(hy:‖y‖+2*v < z.flag) (v':z.dew.X)(he:v'∈closedBall y v): Quiescent z d (d'^s) v' := by
       obtain ⟨a,hΩ,V,hV,hL',hVk,hVF,hη⟩:= hS; let f:=z.dew.β; let g:=windC z d; have h: loyal D.B T P.L d (d'^s) f t D.ρ z.budget v':= hx _ _ D.S _ _ h.page h.binder (h.depart ▸ hP'.stitches) hT' hL (hT' ▸ (show T.up.Bounds _ σ C (loopBill G P.L t) from hP'.staples)) Λ (hL ▸ hl) D.ρ h.scout h.agency D.label V hV hL' hVk z.budget B' a f (Classical.choice hΩ) hb hVF y hη hy _ he; exact ⟨h.2.1,h.1,h.2.2⟩
    exact ⟨fun z hz=> he x hp hh z hz, he 0 h.zeroSeat (by rw [norm_zero,zero_add]; apply (le_add_of_nonneg_left (norm_nonneg x)).trans_lt hh) 0 (mem_closedBall_self hv)⟩
section broad
omit W hm
private lemma inherit_course (M:Meter)(Y:ℕ→ℕ)(hY:Tendsto Y atTop atTop): (∀ e,M.Rush e fun i=> M.pow (-(Y i:ℝ)) i) ∧ M.Rush 0 (fun i=> M.pow ((Y i+1:ℝ)⁻¹) i) := by
   have ht:Tendsto (fun i=>(Y i:ℝ)) atTop atTop:= (tendsto_natCast_atTop_atTop).comp hY
   refine ⟨fun e b h=>?_ ,fun b hb=>?_ ⟩; · filter_upwards [M.grows.eventually_ge_atTop 1,ht.eventually_ge_atTop (-b)] with i hi hv ; rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _)]; exact Real.rpow_le_rpow_of_exponent_le hi (by linarith only [hv])
   filter_upwards [M.grows.eventually_ge_atTop 1, ht.eventually_ge_atTop b⁻¹] with i hi ht ; rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _)]; exact Real.rpow_le_rpow_of_exponent_le hi (inv_le_of_inv_le₀ hb (by linarith only [ht]))

include W hm hk hn hQ hg hO
-- Uniform warm limit. Powers defined only for d. Ambient exp.H.At least two schemes chairs.e (could reframe P). Conditions discharge later.
theorem commission {v a:ℝ} (hr:Capture.race<τ)(he:τ<0)(hu:τ*(k+1)<v)(hv:v<0)(ha:v<a) (C':ℝ) (J:BareRates.pre G σ' C' (n+3)): ∃ r:ℕ, ∀ᶠ x:ℝ in atTop, ∀ z:StagePort G U O X k P.L σ C M n, x=z.pearlRide→Rung P W B A z R σ' C' r Q→ ∀ v,Buys P W B z R a v:= by
   by_contra H; push Not at H;
   let Y:=StagePort G U O X k P.L σ C M n; let U'(x:ℕ)(y:Y):= Rung P W B A y R σ' C' x Q; let F(y:Y):=∀ v,Buys P W B y R a v;
   have hf (i:ℕ): ∃ z:Y, (i:ℝ)≤ z.pearlRide∧U' i z∧ ∃ y,¬ Buys P W B z R a y:= by obtain ⟨x,⟨v,hv,H,h'⟩, hx⟩:= ((H i).and_eventually (eventually_ge_atTop (i:ℝ))).exists; obtain ⟨v',he,hf,h⟩:=h'; exact ⟨v,hv ▸ hx,H,v',fun x=> h (x he hf).1 (x he hf).2⟩
   choose v' h₀ h₁ h₂ using hf; let V (i:ℕ):=v' i;
   let f(i:ℕ):=(V i).pearlRide; have hp :Tendsto f atTop atTop:= tendsto_atTop_mono h₀ (tendsto_natCast_atTop_atTop (R:=ℝ)); let g:= fun i=> betaF G (f i) P.L; let M':Meter:= ⟨g,(YM.Work.E09.betaF_growth G P.L).comp hp⟩;
   have hX (i:ℕ):= (h₁ i|>.ship); choose J' hI ht hS using hX; have h:Travel M' Q V:= by
        have hg:Tendsto J' atTop atTop:= tendsto_atTop_mono (f:=id) hI tendsto_id;
        refine ⟨hQ,Eventually.of_forall fun i=> (h₁ i).depart,hp,Eventually.of_forall fun _=> rfl,⟨(fun i=>(J' i:ℝ)),(fun i=> ((J' i:ℝ)+1)⁻¹),J',(inherit_course M' J' hg).1,(inherit_course M' J' hg).2, Eventually.of_forall (fun i=> ⟨ht i,hS i⟩)⟩,?_ ⟩ -- Ledger shape
        have hw:= inherit_course M' id tendsto_id
        have hi : M'.Rush 0 (fun i=> (Fintype.card (Site (V i).dew.c):ℝ)):= by
            have hK:= Meter.Rush.grounded hQ.uses hp (Eventually.of_forall (fun x=> (show M'.β x=betaF G (f x) P.L from rfl))); refine Current.Rush.bb hK (Eventually.of_forall fun i=> ⟨Nat.cast_nonneg _,?_⟩); exact ((hS i).truePE.stitches.primary).trans_eq (h₁ i).depart
        refine ⟨fun j e hp hv=>?_ ,?_ ⟩
        · refine ⟨_,hw.2,M'.eventual.mono fun i hi=> ⟨Real.rpow_nonneg hi.le _,(h₁ i).healthy _ _ hp hv⟩⟩
        refine Meter.Rush.take (hi.bind ((Fintype.card (Loc G 1)):ℝ)) (Eventually.of_forall (fun i=> ?_)); push_cast; rw [show Fintype.card _=_ from (show Fintype.card (Lines G (V i).dew.c 1)=_ from Fintype.card_prod ..),Nat.cast_mul];
   obtain ⟨d,hd,hP⟩:= lifting_budget (O:=O) (X:=X) (M:=M) (k:=k) P W B A hm (show 2≤n from hk.trans hn) J (Classical.choice (Planned.JetPort.purchase W.table W.table_exists _)) hQ; obtain ⟨s,hU,hW⟩:= h.wage hk hn hg hO hd hr he hu hv ha -- args
   obtain ⟨i,hi,hj⟩:= (hW.and (hp.eventually (hP _ hU))).exists; obtain ⟨z,hz⟩:=h₂ i;
   apply hz; intro Y' he; exact hi z (hj (V i) rfl i (h₁ i) z Y' he)
end broad
end Bookend
end Provision
end YM.Contacts.Junction
