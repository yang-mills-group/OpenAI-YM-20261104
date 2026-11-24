import YM.OPE.Compatible.Brou.View
import YM.OPE.Compatible.Glyph.Ivory
/-! # actual planner.Moves meet all adiabatic. Keep pre vs post witnesses. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Set MeasureTheory Lattice Laurent Tree RG Wilson Stationary Next.Free Precision PhysicalNext PhysicalNext.ThroughLaunch RG.Supply Org
open scoped Topology BigOperators Classical
variable {n c f:Side} {G :Gauge} {s :Sheet G} {l:ℕ→ℕ}{D:Rolls (ThroughLaunch.raise s l)} {θ : Protection D}{V: Delays θ}{Y:Bar V} {W: Wait Y}
variable {T: MapPrices}{K:Sponsor G}{A: Levels G}{M: Horizon A}{O:ChartRatio G}{F:PostCost D}
variable {g:Kin M (Next.Foundations.chart G)}{R:Kin M O}
variable {H:Seasons K}{m N:ℕ}
-- Freeze.P.Omega.A.S.Levels
structure Lend (s:Sheet G) (H:Seasons K):Prop where
       coreQ : s.kernel=K.K
       top i : (s.profile i).clip.direct ≤ K.γ i
       widths i:H.peak i ≤ (s.profile i).width
       arity i: (s.profile i).paths ≤ H.gradeL i
variable (h:Paid W A)(hK:Lend s H)(hm:m<N)(hp: Torrent K.X T K.l F A M g)
local notation "J" => A.clock.J
local notation "Y!"=> A.clock
local notation "Λ!"=> A.clock.loopCap
include hp h hK hm
lemma atm : TicketBed K (J m) (A.params m).clip (location A N m) (M.H N m) := by
       obtain ⟨X,W',u,hW,hS,hE,hτ,hV,hD,hN,hi,hr,ht,hH,-⟩:=hp.layer
       have ht:A.params m=s.profile (J m):= h.stage ▸ (by rfl)
       have hh:A.clock.kernel=K.K:= h.kernel.trans hK.coreQ
       rw [hH.other N m hm,hE.1]
       exact ⟨by rw[ht];exact hK.top _,hh ▸ hS.1 N m hm.le,hW.covers N m hm.le,hW.traces N m hm.le,fun i=>hW.oath N m i hm.le⟩
section
omit h hK hm hp
noncomputable def assigned (h:Paid W A)(hK:Lend s H)(hm:m<N)(hp: Torrent K.X T K.l F A M g):Alps K H (J m) (Λ! m) := by
       have hA:A.params m=s.profile (J m):= h.stage ▸ (by rfl); refine ⟨_,_,_,g.path N m, atm h hK hm hp,hp.paths.links _ _ hm.le,budget_mono _ _ (hp.paths.cap N m hm.le) ?_ (H.positive ..) ?_ le_rfl⟩ <;> rw[hA]; exact hK.widths _; exact hK.arity _
end
omit hp h hK hm
section
variable (R)
lemma step_lit (A:Levels G)(m:ℕ):∀ᶠ p:ℕ in atTop,Bid.Larger (G:=G) (A.clock.op m p):=by
        filter_upwards [(bound_climb G A m).eventually_gt_atTop 1,(bound_climb G A (m+1)).eventually_ge_atTop (100*Pressure.macroR (A.clock.op m 0).patch)] with i hi h using ⟨(A.blocks m i).branches,h,hi⟩
variable (C:ChartRatio G)
private lemma sizer {i j:ℕ}{p q:Clip}{u v:PathData G}{M:Flight i j}{k:KernelChoices}{y h z w:ℝ}(hx:f.val=c.val*M.L.val)(hl:
      let X:= M.visit k hx; let Y':= Woody.forest X.ratio M.odd; Bid.Larger (G:=G) X ∧ ∃ g, Critical Y' p u g ∧ ClassicalMatch Y' p q u v g∧ FiniteBound Y' u v p q w C g y h z) :
      let X:= M.visit (c:=c) (f:= c*M.L) k rfl; let Y':= Woody.forest X.ratio M.odd; Bid.Larger (G:=G) X ∧ ∃ g, Critical Y' p u g ∧ ClassicalMatch Y' p q u v g∧ FiniteBound Y' u v p q w C g y h z:= by
       have hH: f = c*M.L:= PNat.eq hx; subst f; exact hl
-- param normalization; no A casts
include hm in
lemma scaling (ht:R.Planned F): Pilgrim G (destination A N m) A.clock.kernel (A.params (m+1)).clip (A.params m).clip (R.path N (m+1)) (R.path N m) (R.alpha N m) O:=by
      let i:= J (m+1); obtain ⟨k,hk⟩:= eventually_atTop.mp (step_lit A m); refine ⟨(fun i=>A.S.side m (i+k)), (bound_climb G A m).comp (tendsto_add_atTop_nat k),F.Γ i,F.c i,A.clock.loopCap (m+1),F.posC _,?_⟩; intro v; let p:= v+k; let F':= Woody.forest (A.clock.op m p).ratio (A.S.block_odd m); exact sizer O (show (A.S.side (m+1) p).val= (A.S.side m p).val*(A.S.block m).val from (A.clock.op m p).sizes) ⟨hk p (by omega),R.stationary N m p F',(ht.critical _ _ _ hm F').1,ht.classicalPart _ _ _ hm F',ht.retains _ _ _ hm F'⟩
end

include h hK hp
lemma campaign (hN:m+1<N):Charm (A.S.block m) (assigned h hK hN hp) (assigned h hK (Nat.lt_trans (Nat.lt_succ_self m) hN) hp) (g.alpha N m) (Next.Foundations.chart G):=by
       have he:A.clock.J m≤A.clock.J (m+1):= A.fits.mono (Nat.le_succ m); have hv:= A.fits.stepSlow m; have hA:K.K=A.clock.kernel:=(h.kernel.trans hK.coreQ).symm
       refine ⟨⟨A.clock.adm _,A.clock.adm _,by omega⟩,destination A N m,rfl,rfl,loc_land A N m (by omega),?_⟩; change Pilgrim G _ K.K _ _ (g.path _ _) (g.path _ _) _ _; -- rewrite careful
       change Pilgrim G _ K.K (A.params (m+1)).clip (A.params m).clip _ _ _ _; rw [hA]; exact scaling (m:=m) (N:=N) g (by omega) hp.paths
end YM.OPE.Votive
