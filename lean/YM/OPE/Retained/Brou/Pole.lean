import YM.OPE.Compatible.Brou.Pole
import YM.Integration.WilsonMatrixTicketRetarget

/-! The physical OPE estimate on the retained kinetic horizon and transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive.Retained
open Function Filter Set MeasureTheory Lattice Laurent Tree RG Wilson Stationary Next.Free Precision PhysicalNext PhysicalNext.ThroughLaunch RG.Supply Org
open scoped Topology BigOperators Classical
variable {n c f:Side} {G :Gauge} {s :Sheet G} {l:ℕ→ℕ}{D:Rolls (ThroughLaunch.raise s l)} {θ : Protection D}{V: Delays θ}{Y:Bar V} {W: Wait Y}
variable {T: MapPrices}{K:Sponsor G}{A: Levels G}{M: Horizon A}{O:ChartRatio G}{F:PostCost D}
variable {g:Kin M (Next.Foundations.chart G)}{R:Kin M O}
variable {H:Seasons K}{m N:ℕ}
-- Freeze.P.Omega.A.S.Levels
variable (h:Paid W A)(hK:Lend s H)(hm:m<N)(hp: Imperial K.X T K.l F A M g)
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
noncomputable def assigned (h:Paid W A)(hK:Lend s H)(hm:m<N)(hp: Imperial K.X T K.l F A M g):Alps K H (J m) (Λ! m) := by
       have hA:A.params m=s.profile (J m):= h.stage ▸ (by rfl); refine ⟨_,_,_,g.path N m, atm h hK hm hp,hp.paths.links _ _ hm.le,budget_mono _ _ (hp.paths.cap N m hm.le) ?_ (H.positive ..) ?_ le_rfl⟩ <;> rw[hA]; exact hK.widths _; exact hK.arity _
end
omit hp h hK hm
include h hK hp
lemma campaign (hN:m+1<N):Charm (A.S.block m) (assigned h hK hN hp) (assigned h hK (Nat.lt_trans (Nat.lt_succ_self m) hN) hp) (g.alpha N m) (Next.Foundations.chart G):=by
       have he:A.clock.J m≤A.clock.J (m+1):= A.fits.mono (Nat.le_succ m); have hv:= A.fits.stepSlow m; have hA:K.K=A.clock.kernel:=(h.kernel.trans hK.coreQ).symm
       refine ⟨⟨A.clock.adm _,A.clock.adm _,by omega⟩,destination A N m,rfl,rfl,loc_land A N m (by omega),?_⟩; change Pilgrim G _ K.K _ _ (g.path _ _) (g.path _ _) _ _; -- rewrite careful
       change Pilgrim G _ K.K (A.params (m+1)).clip (A.params m).clip _ _ _ _; rw [hA]; exact scaling (m:=m) (N:=N) g (by omega) hp.paths
end YM.OPE.Votive.Retained

