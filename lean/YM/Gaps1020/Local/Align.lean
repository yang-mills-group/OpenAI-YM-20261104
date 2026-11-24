import YM.Gaps1020.Local.Gown
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Renew
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time Rain Mallow Roost UVNext.CouplingReset Daisy.Charity.RG12
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open YM.ConnectedActivityE6.Blaze.Thermal1020
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Ovens Pipes Rack Averaging WilsonStartup
variable {G:Gauge}
variable {n: Side}{p:BudgetPoint}{X:Listing G n}{Y:PathData G}{K:Clip}
    {a b h H v c w f:ℝ}{J J₀ J₁ : Collection.Source G n}
local notation "B"=> shelves X Y p
local notation "Δ!" A => Averaging.delta (X.read A)
local notation "E₀" A:max x:max => Collection.branch X Y K p A x
section combine
variable (hG:G.Simple) (P:Activities G n)
    (hX:P.Valid p H w)
include hG
lemma delta_split (hg:J.logRead=J₀.logRead+J₁.logRead) (hp:Collection.Local X p J a b)(hr:Collection.Local X p J₀ v c)(he:Collection.Local X p J₁ h H) : delta (X.read J)=delta (X.read J₀)+delta (X.read J₁):= by
   unfold Averaging.delta Averaging.total; let T (A:Collection.Source G n) := censusAt (X.read A) 0 axes01 axes01
   have hT(i):T J i=T J₀ i+T J₁ i:= by
      unfold T censusAt; change (if _=0 then projection _ (J.logRead i) _ _ else 0) = (if _=0 then projection _ (J₀.logRead i) _ _ else 0)+(if _=0 then projection _ (J₁.logRead i) _ _ else 0); dsimp only [Listing.read]; split
      next h'=>
         apply (sub_eq_iff_eq_add.mp) -- rhs? sub J−J₁
         exact (projection_sub (X.reg i) (hp.smooth i) (he.smooth i) axes01 axes01).symm.trans (by rw [show J.logRead i-J₁.logRead i=J₀.logRead i from sub_eq_of_eq_add (congr_fun hg i)])
      next h' => ring
   change ∑' i,T J i=(∑' i,T J₀ i)+(∑' i,T J₁ i); rw [funext hT, Summable.tsum_add]; exact hr.projects.seriesAt hG ..; exact he.projects.seriesAt hG ..
lemma alignment (α : ℝ)(hR:J.logRead=J₀.logRead+J₁.logRead) (hp:Collection.Local X p J a b)(hr:Collection.Local X p J₀ v c)(he:Collection.Local X p J₁ h H) :
    let X:= drawer G n
    let V:= X.pours (widen B (E₀ J α)); let W:= X.pours (widen B (E₀ J₀ α)); let Z:=X.pours (widen B (E₀ J₁ 0)); V.E=W.E+Z.E:=by
   intro Y' V W Z; have hh(i:ℕ): ((E₀ J α)).regular i=((E₀ J₀ α)).regular i+((E₀ J₁ 0)).regular i:= by
      have hs := delta_split hG hR hp hr he; have ht := Collection.archive_sub (X:=X) hp.smooth hr.smooth (c:=K) Y α (Δ! J) (Δ! J₀) ((numbering (EKey n)) i)
      apply Eq.trans (b:=((E₀ J₁ 0)).regular i + ((E₀ J₀ α)).regular i) _ (add_comm ..); apply sub_eq_iff_eq_add.mp
      rw [show ((E₀ J α)).regular i- ((E₀ J₀ α)).regular i=_ from ht, hs,add_sub_cancel_left]; change _= Collection.archive _ _ _ _ _ _ _; unfold Collection.archive; rw [show (J-J₀).logRead=J₁.logRead from (by change J.logRead-J₀.logRead=_; rw [hR,add_sub_cancel_left])]
   funext i; change stuff (upE B) ((E₀ J α)).regular i=stuff (upE B) ((E₀ J₀ α)).regular i + stuff (upE B) ((E₀ J₁ 0)).regular i; by_cases h':i∈Set.range (upE B); swap
   · rw [Progress.DirectedRecipe.blank _ _ h',Progress.DirectedRecipe.blank _ _ h',Progress.DirectedRecipe.blank _ _ h',add_zero]
   obtain ⟨i,rfl⟩:=h'; rw [stuffed,stuffed,stuffed]; exact hh i
-- paste the actual hard reads/tests. Claim only Valid, not payment or moves for approximated vertex with a recomputed K. `K` never differ here. Strong price *relative to linearized gauge* in same δ. Parameter proof bound is used, not a prescription made by coefficient fitting.
def coverWorld (P:Activities G n) (X:Listing G n)(p:BudgetPoint)(Y:PathData G)(K: Clip)(J:Collection.Source G n)(α:ℝ): Activities G n where
    reg:= P.reg
    E := ((drawer G n).pours (widen (shelves X Y p) (branch X Y K p J α))).E
    K:= P.K
    forced:= P.forced
lemma pasted (P Q : Activities G n)(h:Collection.Local X p J a b) (hX:P.Valid p H w)(he:P.reg=(drawer G n).reg) (hk:Y.Bounds K v c f)(ht:WilsonStartup.Decent K p)(hw:Geo.Width p K v)(hf:20<n.val)(α:ℝ)(hs : Q=coverWorld P X p Y K J α): Q.Valid p (regularNeed G p K v c α a) w:=by
   subst Q; let Y':= (drawer G n).pours (widen B (E₀ J α));
   have hp:Payments.Fittings (E₀ J α) B p:= h.fittings hG hk ht hf ..
   have ht':= (Rack.preserves B (E₀ J α) p)
   have hh : ((shelves X Y p).pours (E₀ J α)).EBound p (regularNeed G p K v c α a):= by
      obtain ⟨u,hu,hb⟩:= h.cheap
      obtain ⟨he,-⟩:= Local.quote_family hk ht hw α _ hu hb (Averaging.delta_bound hG h.projects)
      exact ⟨_,fun i=> Local.quote_regular (v:=J) hG hk ht α _ hu h.smooth (numbering _ i),fun x=> Cost.equiv (numbering _) (he x)⟩
   have hv: (coverWorld P X p Y K J α).reg= Y'.reg:= he
   let G':= coverWorld P X p Y K J α; have hL : G'.RegularFamily p:=by
      have hF:= ht'.regular hp.regular
      refine ⟨fun i=> ?_,fun i=> hF.at_flat i,fun i=>?_⟩
      · change p.Regular _ (Y'.E i); rw [hv]; exact hF.smooth i
      rw [hv]; exact hF.vanish i
   have hK:G'.ForcedFamily p:=⟨hX.forced.sym,hX.forced.symtest,hX.forced.meas,hX.forced.meas_test,hX.forced.reads,hX.forced.reads_test,hX.forced.permit⟩
   refine ⟨hL,hK,fun s b=> ?_,?_,hX.boundK⟩
   · obtain ⟨J'⟩:= hp.moves s b; let J:= on_shelves J'
     obtain ⟨p⟩:= hX.moves s b; rw [coverWorld,he]; exact ⟨J.ep,p.kp,J.reg_site,J.reg_support,p.forced_support,p.forced_inventory,p.forced_tests,J.valuesE,p.valuesK⟩
   rw [coverWorld, he]; exact ht'.Ebound hh

omit hG
lemma eBudgetSub (A F C : Activities G n) (hA:A.reg=C.reg)(hB:F.reg=C.reg)
    (h:A.E=C.E+F.E)(ha:A.Valid p a w)(hb:F.Valid p b w) : C.EBound p (a+b):= by
   obtain ⟨k,hk,hP⟩:= ha.boundE; obtain ⟨g,hg,hG⟩:= hb.boundE
   refine ⟨k+g,fun i=> ?_, fun i=>?_⟩
   · have hh i:C.E i=A.E i-F.E i:= eq_sub_of_add_eq (by rw [h]; rfl)
     have he':p.Regular (C.reg i).support (A.E i):= hA ▸ ha.regular.smooth i; have hf:p.Regular (C.reg i).support (F.E i):= hB ▸ hb.regular.smooth i
     rw [hh]; exact sup_sub he' hf (hA ▸ hk i) (hB ▸ hg i)
   have he:= hP i; rw [hA] at he; have hs:= hG i; rw [hB] at hs
   convert! budget_plus he hs using 1; ext p; split <;> simp [BudgetPoint.mass,mul_add]
end combine
end YM.GapsLocal.Renew
