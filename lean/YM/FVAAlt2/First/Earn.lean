import YM.FVAAlt2.First.Pay
import YM.FVAAlt2.Shop.Match
/-! At ε convert Full.row to the precise regulator estimate via MS.Marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Function Finset Filter Topology Lattice Labels Source
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Local.Physical MS.Land MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open MS.Book.Convolve MS.Native.Studio MS.Native.Paint MS.Native.Wilsonian
open MS.Puff MS.Puff.Mom MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Dial MS.Tide MS.Swirl MS.Swirl.Near MS.Fleet MS.Rake MS.Vane MS.Vista
open PowerSeries (C coeff)
open Pert PertExtension Precision Billing SchemeRG11.Sway SchemeRG11.Sway.Lam SchemeRG11.Atoll SchemeRG11.Pile Lobby
open Home
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {W:Type}[LinearOrder W][Fintype W]{G:Gauge}{n:Side}{d k:ℕ}{B:Deck G}{F:Frames G}
variable (V:Prescription B)(y ε:ℝ) (x:W→ Site n)(p:W→Rake.Label B)
local notation "CZ"=>PowerSeries ℂ
local notation "RZ"=>ExtraBook B
-- factor layout.S
abbrev atPaid (x:W→Site n)(ε:ℝ)(p:W→Rake.Label B):CZ := C ((ε:ℂ)⁻¹ ^ wt p)*rawL x p
abbrev boardX(x:W→Site n)(ε:ℝ) := ∑ q:(i:W)→Glyph B (p i).h,(∏ i,changePrice V y p ε i (q i)) * redo V.team y (atPaid x ε (fun i=>owner (q i)))
lemma earned(hw: ε≠0): boardX V y p x ε=C ((ε:ℂ)⁻¹ ^ wt p)*postP V y p x:=by
 unfold boardX postP; rw [Finset.mul_sum]; refine sum_congr rfl fun q _=>?_
 let u(i:W):= owner (q i); let U:= rawL x u; let c:= C (R:=ℂ); let z:ℂ:=ε
 rw [show redo V.team y (atPaid x ε u)=C ( z⁻¹ ^ wt u ) * redo V.team y U from by unfold atPaid; rw [ ← PowerSeries.smul_eq_C_mul,map_smul,PowerSeries.smul_eq_C_mul ] ]
 have h0:z≠0:=by unfold z; exact_mod_cast hw
 unfold changePrice; rw [Finset.prod_mul_distrib]; have ht(q:W→Rake.Label B) : c (z⁻¹ ^ wt q)= ∏ i:W,c (z⁻¹ ^ (q i).h):=by rw [← map_prod c,Finset.prod_pow_eq_pow_sum]
 have hb : (∏ i:W, c (z^((u i).h-(↑(p i).h:ℤ))))*c (z⁻¹ ^ wt u)=c (z⁻¹ ^ wt p):= by
    rw [ht u,ht p,← Finset.prod_mul_distrib]; refine prod_congr rfl fun i _=>?_ ; rw [← map_mul, zpow_sub₀ h0, zpow_natCast,zpow_natCast, inv_pow, inv_pow]; congr 1; field_simp
 change (∏ i:W,c (z^((u i).h-(↑(p i).h:ℤ)))) * _ * (c _ * _)=c _ * _; rw [← hb]; ring
variable (P:FormalOPE.RG10.Position.Plan F)(hl: P.liftOff=LoftPP F)
local notation "Y"=>seats P.liftOff P.certified
local notation "pTm"=> Full.profile
lemma prod_apply2 {I R S:Type*}[CommRing R][Fintype I](p q:I→S→R)(c:I→R)(hp:∀ i,p i=c i • q i): ∏ i:I,p i=(fun _=> ∏ i:I,c i)*(∏ i:I,q i):=by funext y; simp_rw [hp,Finset.prod_apply,Pi.mul_apply,Pi.smul_apply, smul_eq_mul,Finset.prod_mul_distrib, Finset.prod_apply]
lemma payment {T:Type}[Fintype T] (p q:T→Pert.Orb.JetArray (SchemeRG11.Sway.Land G n))(c:T→ PowerSeries ℂ)(hx:∀ i,p i=c i • q i)(hp: ∀ i,Pert.Orb.Ready (q i)): Lentry (∏ i:T,p i)=(∏ i:T,c i)* Lentry (∏ i:T,q i):= by rw [ prod_apply2 p q c hx, Lentry_scale (Pert.Orb.Ready.prod fun i _=> hp i)]
lemma root_entry(o:Site n)(i:Rake.Label B): Lsup o ε (dream ε (realCast (enterL i)))= C ((ε:ℂ)⁻¹ ^ i.h) • Lsup o 1 (dream 1 (realCast (enterL i))) := by
 have he : @Orbis G ( enterL i ) i.h i.item.1.val:= price_grade i.item.2
 exact dilation _ ε he _ rfl
lemma root_fields (q:W→Pol G) (he:∀ i, q i=realCast ( enterL (p i) )): Lentry (∏ i,Lsup (x i) ε (dream ε (q i)))=atPaid x ε p:=by
 simp_rw [he];
 let c:=fun i:W=> C ((ε:ℂ)⁻¹ ^ (p i).h); let A(i:W):= Lsup (x i) 1 ( dream 1 (realCast (enterL (p i))))
 trans (∏ i:W,c i)* Lentry (∏ i:W,A i); exact payment (fun i=> Lsup (x i) ε ( dream ε (realCast (enterL (p i))))) A c (fun i=> root_entry ε (x i) (p i)) (fun i=> lsup_ready _ _ _)
 unfold c; rw [← map_prod, Finset.prod_pow_eq_pow_sum]; rfl
include hl
lemma placedL (i:Glyph Y d): Full.sections d F (peg Y i F)= realCast (enterL (owner i)):= by
 have he := @mast_lifts _ _ _ P i.2 -- dependent occurrence problematic? he type includes Y.
 rw [owned]; change ( RawLabels.physicalLabel F d _ ).val=_; rw [ show RawLabels.physicalLabel F d=(P.liftOff.lift d) from (by rw [hl];rfl), P.certified.shelf ]; change _ = realCast (price i.2.2); rw [price_is]; exact congr_arg Subtype.val he -- defeq with raise? check
variable {m:ℕ} (X:Fin m→ Site n) (HN:Pert.Orb.Admissible n)
include HN
theorem row_paid (v:Fin m→Glyph Y d) : Full.row d F ε X (fun i=> mast Y d F (v i))= atPaid X ε ( owner ∘ v ) := by
 apply Eq.trans (SchemeRG11.Sway.axisCut (d:=d) ε HN X F (fun i=> mast Y d F (v i)))
 change Lentry _ = _
 have hh:= root_fields ε X ( owner ∘ v ) (fun i=> Full.sections d F (peg Y (v i) F)) (fun i=> placedL P hl (v i))
 exact hh

omit hl HN
variable {I:Type}{T:Trial I W}{U:MS.Land.Booked B}{μ:ℝ}{l:Filter I}{A:Terrify W I}
variable {D:ChartRatio G}(h:LocalRatio D)(X:MS_Data G U)
local notation "g"=> Rake.Label.h∘p
def cash(T:Trial I W)(μ:ℝ)(k:ℕ)(i:I):ℂ:= coeff k (boardX V (μ-T.profile.θ i) p (situated T i) (spacing T i))
include D h
open PeakT
lemma seeded (hp: coherentPl U X RZ p T μ true V l A)(i:I) (k:ℕ) (he: Pert.Orb.Admissible (dimT T.side i)) : fare g T.profile (ordZ A) univ k i= cash V p T μ k i:= by
 let n:= dimT T.side i; let pp:= T.profile; let a:=μ- T.profile.θ i; letI : Module.Free ℝ (SchemeRG11.Sway.Land G n):=Module.Free.of_divisionRing ℝ (Land G n); let hQ := Module.finBasis ℝ (SchemeRG11.Sway.Land G n); let hT:= Module.finBasis ℝ (ScalarGhost G n)
 have hs:ordZ A univ k i= coeff k (postP V a p (situated T i)):= congrFun (classicalμ (τ_nil ..) (hp.cost i univ) (ent_p (T.head i) (fun w=> T.off w i) h he V a p hQ hT)) k
 rw [fare,Pi.mul_apply, hs,cash,earned,PowerSeries.coeff_C_mul ]; rotate_left
 · exact (Real.exp_pos _).ne'
 unfold MS.Tide.higher Port.τ spacing; rw [ Real.exp_neg ]; rw [show ( ↑(Vane.charge (Rake.Label.h∘p) univ):ℤ)=↑(wt p) from rfl,zpow_natCast, Complex.ofReal_pow,Complex.ofReal_inv,inv_inv]
-- arbitrary Takes.I  -- hypotheses stage.P
open PeakT
lemma visits_β (hi:Dial.Uses T l μ)(hg:G.Simple)(hv: TaylorOKPl X RZ V)(k:ℕ): twin l T.profile mildG (cash V p T μ k) (fun i=> tour X p μ (testP T i) univ k):= by
 obtain ⟨A,hA⟩:= Dial.check_tPl X RZ p T hv hi hg true; obtain ⟨hS,hV⟩:= hA.bouquet univ k; refine ⟨hS,PeakT.fromζ hV ?_⟩; filter_upwards [Billing.SideFunding hi] with i he; rw [Pi.sub_apply,Pi.sub_apply, seeded V p h X hA i k he]
end YM.FVAAlt2.Pairing
