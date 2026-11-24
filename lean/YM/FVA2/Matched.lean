import YM.FVA2.ColumnPrice
import YM.MS.Dial.Signals

/-!
# Bare massless inversion-even coefficients ↔ lattice-token choice in YM.MS

Registry (`Matched`) chooses a `Land.Prescription` solely by the existing MS
endpoints; this is the *a-dependent* bare coupling/field choice achieving MS
correlations. No phase or shape fed to this choice. It is common to
MS.Tide.remove and MS.Dial.LPT_to_MS comparison conclusions (for *both*
constructor choices). There is still a job to align a physical *continuum*
frame. Index `b=false` is never used here (no silent change of quotient).
Points estimates using supplied definitions, no iterated-subsequence reading of
IR/UV unless Trial definition forces. Source-connected exponent evaluated by
subset log on ordinary moments. No estimates postulated and no perturbative
radius. Keep hypotheses Physics.Deck + native.Real formula; can use `realF`
dictionary in `WilsonSource`.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Matched
open Function Filter Topology
open MS MS.Local.Physical MS.Plane MS.Landau MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom MS.Puff.SplitP MS.Native.Wilsonian MS.Theater MS.Menus MS.Fleet MS.Swirl MS.Swirl.Near
open MS.Rake MS.Land MS.Tide MS.Orbit MS.Tone MS.Tide.PeakT MS.Dial
open Source Channel Score Lattice
open scoped Topology Classical
variable {G: Gauge} {B: Deck G} {O: Booked B} (b: MS_Data G O) (φ:NativeDictionary B)
variable {I W:Type} [LinearOrder W] (p:Trial I W)(A:Land.Prescription B)
variable (μ:ℝ) (w: W→ Label B) (l: Filter I)

-- order.K.Bare reexpression. Operators types.Full Eta computed. Note names: b here denotes MSLaw data.
abbrev rate (P:Land.Prescription B)(μ:ℝ)(θ:ℝ):= Clock.rate P.team (μ-θ)
lemma dimT_even (L:I→ Side)(i:I): Even (dimT L i).val:= by rw [dimT,cap_val]; exact ⟨ _, two_mul _ ⟩
local notation "dκ"=> Label.h ∘ w
local notation "Ξκ"=> tFees A w -- define

def tFees (P:Land.Prescription B)(z:W→ Label B) : (w:W)→ Acts B (Label.h ( z w )) := fun w=> P.fees (z w|>.h) (z w|>.item)
-- genuine bare total: pre-log.Also useful for positions.Op.S.
def folio (i:I) (s:Finset W): PowerSeries ℝ := ticketRead φ (dimT p.side i) dκ A.team (μ-p.profile.θ i) (tFees A w) (p.head i) (fun j=>p.off j i) s

def pre i s := Score.netE (folio φ p A μ w i s)
def ordinary : Fleet.Terrify W I:= fun s n i=> pre φ p A μ w i s n
def connected : Fleet.Terrify W I:= fun s n i=> MS.Puff.Log.Meter Trunk (marked W) (pre φ p A μ w i) s n

local notation "μF"=> ordinary φ p A μ w
local notation "MF"=> connected φ p A μ w
local notation "↧A"=> fare dκ p.profile
local notation "νC"=> Dial.coherent O b φ.book w p μ true A l -- V
local notation "νS"=> scalePhysics p.profile O b μ A φ.book w p.off p.head p.side true l
-- raw endpoint
lemma raw (i:I)(s:Finset W)(X:T ℂ) : PhysicalSum G A.team (μ-p.profile.θ i) (dimT p.side i) true s (fun z=>p.off z i) (p.head i) ( ApplyM φ.book (Stripped A.team) A w ) X ↔ pre φ p A μ w i s=X:= Channel.finite_bridge _ (dimT_even p.side i) _ (tFees A w) _ _ _ _ _ _

lemma treeCost {V:Fleet.Terrify W I} (h:Dial.Cutoff φ.book w p μ true A V)(hx:V ∅=0): MF=V ∧ μF=ordZ V:= by
    have hf(i:I): pre φ p A μ w i = fun s=> bury i s V:= funext fun s=> (raw φ p A μ w i s _).mp (h i s)
    constructor ; swap; · exact funext fun s=> funext fun n=> funext fun i=> congr_fun (congr_fun ( hf i ) s) n
    let Y(i:I):= fun s n=> V s n i; funext s n i; unfold connected; rw [hf i,(show MS.Puff.Log.Meter Trunk ( marked W ) (fun s=> bury i s V)=Y i from (MS.Puff.Log.recheck _ _ _ (show Y i∈ allIndex _ _ from fun _ _ _ _=> Submodule.mem_top) (Tide.pointed _ hx i)))] -- ambiguous _

structure certified : Prop where
    scale : ∃ Y: Rake.Dance G I W, νS MF Y
    dial : νC MF
    unique : ∀ V:Fleet.Terrify W I, Dial.Cutoff φ.book w p μ true A V → V ∅=0 → V=MF
    pre_log : μF= ordZ MF

lemma certifies (X:Dial.Uses p l μ)(H:∃ V:Fleet.Terrify W I,νC V)(Hp:∃ Z Y, νS Z Y): certified b φ p A μ w l:= by
    rcases H with ⟨ V,hV⟩; rcases Hp with ⟨ Q,Y,hY⟩
    have hF:MF=V:= (treeCost φ p A μ w hV.cost hV.init).1
    have he: Dial.Cutoff φ.book w p μ true A Q:= fun i s=> (X.reality i) ▸ hY.native i s
    exact ⟨⟨ Y, (treeCost φ p A μ w he hY.empty).1.symm ▸ hY ⟩, hF.symm ▸ hV, fun _ h hx=> (treeCost φ p A μ w h hx).1.symm, hF.symm ▸ (treeCost φ p A μ w hV.cost hV.init).2 ⟩

lemma clears (X:Dial.Uses p l μ)(h:G.Simple)(H:TaylorOK b φ.book A): certified b φ p A μ w l:= certifies b φ p A μ w l X (Dial.check_t b φ.book w p H X h true) (Tide.called w p.off X.total X.reality X.upright X.super h X.clear X.wind X.knit H true)

omit [LinearOrder W] in
def AllProfiles (A:Land.Prescription B) : Prop:= TaylorOK b φ.book A ∧ ∀ (W I:Type) [LinearOrder W] (p:Dial.Trial I W)(μ:ℝ)(w:W→Label B)(l:Filter I), Uses p l μ → certified b φ p A μ w l
lemma allProfiles_rake (h:G.Simple): ∃ T':Land.Prescription B, AllProfiles b φ T':= by obtain ⟨P,hP,hq⟩:= Dial.LPT_to_MS φ.book b h; refine ⟨ P,hP, fun W I _ p μ w l H=> certifies b φ p P μ w l H (hq W I _ p l μ w true H|>.exists) ?_⟩; exact Tide.called w p.off H.total H.reality H.upright H.super h H.clear H.wind H.knit hP true
lemma allProfiles_remove (h:G.Simple): ∃ T':Land.Prescription B, AllProfiles b φ T':= by obtain ⟨P,hP,hq⟩:= Tide.remove φ.book b h; refine ⟨ P,hP, fun W I _ p μ w l H=> certifies b φ p P μ w l H (Dial.check_t b φ.book w p hP H h true) ?_⟩; exact hq I W _ p.profile p.side p.head true l w p.off μ H.total H.reality H.upright H.super H.clear H.wind H.knit

-- no postulated uniqueness of A among profiles; MS label inputs and stencil choices fixed.
namespace universal

def deck (G:Gauge): Deck G:= Classical.choice (Deck.setting G)
def book (B:Deck G) : Land.Booked B:= Classical.choice (suitable B)
def data (B:Deck G) : MS_Data G (book B):= Classical.choice (bookedMS (book B))
def kid (B:Deck G): NativeDictionary B:= Classical.choice (diction B)
def policy (B:Deck G)(H:G.Simple) : Land.Prescription B:= (allProfiles_remove (data B) (kid B) H).choose
lemma witnesses (B:Deck G)(H:G.Simple): AllProfiles (data B) (kid B) (policy B H) := (allProfiles_remove (data B) (kid B) H).choose_spec
end universal

-- rate at test-array positions incl diagonal limit. Doesn't assert rate replacing moving by limiting points unless continuity supplies. each i set geometry, only i order/h independent cocycle.
lemma accuracy(c:AllProfiles b φ A)(X: Uses p l μ)(s:Finset W)(n:ℕ): PeakT.twin l p.profile mildG ( (↧A MF) s n ) (fun i=>Dial.book b w μ (testP p i) s n) ∧
  PeakT.twin l p.profile mildG ( (↧A μF) s n ) (fun i=>Dial.tour b w μ (testP p i) s n) := by obtain ⟨_,hq,_,hz⟩:=@c.2 W I _ p μ w l X; exact ⟨hq.ready _ _, hz.symm ▸ hq.bouquet s n⟩
section profile
variable [Fintype W]
lemma on_positions (c:AllProfiles b φ A)(h: Uses p l μ){x:W→Tone.QP} (he: Injective x)(ht:Tendsto (testP p) l (𝓝 x)) (s:Finset W)(n:ℕ): Tendsto ( (↧A MF) s n ) l (𝓝 ( Dial.book b w μ x s n )) ∧ Tendsto ( (↧A μF) s n ) l (𝓝 ( Dial.tour b w μ x s n )):= by
    obtain hc:= @c.2 W I _ p μ w l h; rw [hc.pre_log]; exact Dial.profile_t b φ.book w p hc.dial h he ht s n
end profile
end YM.FVA2.Matched
