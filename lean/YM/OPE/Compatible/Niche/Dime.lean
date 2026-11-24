import YM.OPE.Compatible.Niche.Ruth
/-! # Architecture patch -> Physical. No gauge assumptions outside Step guard. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl
open Function Filter Set MeasureTheory Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input RG.Shoot
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest Stroke.MatchZ
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ ThroughLaunch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι :Type} {G :Gauge} {P: MapPrices}
variable {P':Patch}{n N i j m p l:ℕ}{H:Sponsor G}{T:Seasons H}{s:Sheet G}{t:ℕ→ℕ}
section Story
variable {M:Metals G}{S:Supply.Rolls M.p}{A:Alloy M S}(C:Bolt A) (Y:Factor A)
local notation "E"=>A.B.a.clock
local notation "J"=>A.B.a.clock.J
local notation "jν"=> J (m+1)
local notation "ξ"=>A.B.a.S
abbrev patchP (m:ℕ):= (A.B.a.clock.op m 0).patch
noncomputable abbrev Reach (m:ℕ) := Porte S (J (m+1)) (A.B.a.clock.adm _)
lemma depQ : (ξ).block m=(Reach (A:=A) m).L:=by rw[block_eq A.B.valid m]
set_option quotPrecheck false
private lemma EqPatch (p q:Patch)(h:p.L=q.L)(he:p.J=q.J):p=q:=by cases p; cases q; congr
lemma depR : (A.B.a.clock.op m p).patch= Reach (A:=A) m:=EqPatch _ _ depQ rfl
-- Storage epoch Cash
local notation "Ω"=> A.B.a.S.side m p
local notation "QT"=>A.B.a.S.side (m+1) p
variable {K':ℕ→ℝ}{a:Bid.Worth}{h:G.Simple}(ht:Nest Y C)(hi:m+1<N)
include ht hi h
lemma posture (F:Bandage Y K' a)(r:StepData Ω QT)(hz:r=A.B.a.clock.op m p) :∃ V: Tube G r, PhysicalNext.Repeat.Aroma.epoch (Y.books) (Reach (A:=A) m) (J (m+1)) (J m) r V ((E).hatBeta m) (C.history N p (m+1)):=by
        subst r; let U:= Testing.ships A.B N m p; exact ⟨U,enact Y h _ _ C ht rfl F depR rfl rfl hi⟩
end Story
end YM.OPE.Owl
