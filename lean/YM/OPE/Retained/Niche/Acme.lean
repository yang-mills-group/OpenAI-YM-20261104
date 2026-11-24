import YM.OPE.Compatible.Niche.Dime
import YM.OPE.Retained.Brou.Pole

/-! The physical OPE estimate on the retained kinetic horizon and transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl.Retained
open Function Filter Set MeasureTheory Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input RG.Shoot
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest Stroke.MatchZ
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ ThroughLaunch Zeph
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι :Type} {G :Gauge} {P: MapPrices}
variable {P':Patch}{n N i j m p l:ℕ}{H:Sponsor G}{T:Seasons H}{s:Sheet G}{t:ℕ→ℕ}
section Story
open Next.Foundations
local notation "M"=> ThroughLaunch.bountyV s P t
variable {S:Supply.Rolls (ThroughLaunch.raise s t)}{A:Alloy (ThroughLaunch.bountyV s P t) S}(C:Bolt A)
local notation "E"=>A.B.a.clock
local notation "J"=>A.B.a.clock.J
local notation "jν"=> J (m+1)
local notation "ξ"=>A.B.a.S
set_option quotPrecheck false
local notation "ζP"=> Reach (A:=A) m
local notation "ν"=>A.B.kin.alpha
variable (h: Imperial (s:=s) H.X P H.l A.post A.B.a A.B.M A.B.kin)(hs:Lend s T)
lemma positiveV :1≤ A.B.a.clock.loopCap m:=by
        unfold Calendar.loopCap; have hm:1 ≤ (E).monitor m:= Real.one_le_exp (sq_nonneg _); have hz:= (Real.one_le_rpow hm (A.B.a.fits.thetaRange m).1.le); linarith only [hz]
variable (hx:m<N)
include h hs hx
local notation "B"=>YM.OPE.Votive.Retained.assigned A.B.valid hs hx h
abbrev Capton : Cab T (J m) (s.profile (J m)).clip:=⟨(E).loopCap m,positiveV, B,(congr_arg Stage.clip (params_eq A.B.valid m))⟩
lemma SoftRise : (Capton (A:=A) h hs hx).fees= capL (A.θ.theta (J m)) ((E).hatBeta m):=by change (E).loopCap m=_; rw[(τcoin (c:=E) (k:=m) rfl).2.2.2.2,A.B.valid.theta]
lemma linK : Zeph.fitsW (B) (C.history N p m):=by
        have he := ((C.sticks N p).prices m (Nat.zero_le _) hx.le).1; -- inspect
        constructor; · exact he.clip -- check orientation
        rw[he.path,A.B.bases]; rfl
omit hx
variable (hy: m+1<N)
include hy
local notation "hZ"=> (lt_trans (Nat.lt_succ_self m) hy)
noncomputable abbrev ruler : MatchZ (Reach (A:=A) m) (s.profile (J (m+1))).clip (s.profile (J m)).clip T (J m) (chart G):= ⟨Capton h hs hy,Capton h hs (lt_trans (Nat.lt_succ_self m) hy), ν N m,(by rw[←depQ]; exact YM.OPE.Votive.Retained.campaign A.B.valid hs h hy)⟩
omit h hy -- hs only
-- canonical patch witness and Real Scene stamps. Stint layer need Barrier_P
abbrev ηSz (A:Alloy (ThroughLaunch.bountyV s P t) S)(m p:ℕ):(A.B.a.S.side (m+1) p).val=(A.B.a.S.side m p).val*(Reach (A:=A) m).L.val:=by rw[←depQ]; exact (A.B.a.clock.op m p).sizes
lemma canyon: SlotF (K:=H) (ηSz A m p)=A.B.a.clock.op m p:=by
        generalize hw:A.B.a.clock.op m p=F; have ht:F.patch= Reach (A:=A) m:= hw ▸ depR; have hh:F.kernel=H.K:= hw ▸ A.B.valid.kernel.trans hs.coreQ; cases F with
        | mk x y v=>
           dsimp only at ht hh; subst x y; rfl
end Story
end YM.OPE.Owl.Retained

