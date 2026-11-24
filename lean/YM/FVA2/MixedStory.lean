import YM.FVA2.PenHistory
import YM.FVA2.Matched

/-! # Regulator removal after Wick substitution
 Includes proof of comparison for the explicit Book (with W inverse), and
 actual Tide and Dial on the exact same object *before* that inverse
 is applied to each Section stencil. Demand answer to compare the same points
 and enter with the same coupling.Passing to the tuned sources uses only
 the additional `ceases` projection; no change to estimates as required for
 the regulator schedule. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.MixedStory
open Function Filter Topology
open MS MS.Local.Physical MS.Plane MS.Landau MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom MS.Puff.SplitP MS.Native.Wilsonian MS.Theater MS.Menus MS.Fleet MS.Swirl MS.Swirl.Near
open MS.Rake MS.Land MS.Tide MS.Orbit MS.Tone MS.Tide.PeakT MS.Dial
open Source Track Score Lattice
open Matched (dimT_even tFees)
open scoped Topology Classical
variable {G: Gauge} {B: Deck G} {O: Booked B} (b: MS_Data G O) (φ:Warehouse G)
variable {I W:Type} [LinearOrder W] (p:Trial I W)(A:Land.Prescription B)
variable (μ:ℝ) (w: W→ Label B) (l: Filter I)

local notation "dκ"=> Label.h ∘ w
-- genuine bare total: pre-log.Also useful for positions.Op.S.
def folio (i:I) (s:Finset W): PowerSeries ℝ := ticketRead φ (dimT p.side i) dκ A.team (μ-p.profile.θ i) (tFees A w) (p.head i) (fun j=>p.off j i) s

def pre i s := Score.netE (folio φ p A μ w i s)
def ordinary : Fleet.Terrify W I:= fun s n i=> pre φ p A μ w i s n
def connected : Fleet.Terrify W I:= fun s n i=> MS.Puff.Log.Meter Trunk (marked W) (pre φ p A μ w i) s n

local notation "μF"=> ordinary φ p A μ w
local notation "MF"=> connected φ p A μ w
local notation "↧A"=> fare dκ p.profile
local notation "νC"=> Dial.coherentM O b (φ.native B) w p μ true A l -- V
local notation "νS"=> scalePhysicsM p.profile O b μ A (φ.native B) w p.off p.head p.side true l
-- raw endpoint
lemma raw (i:I)(s:Finset W)(X:T ℂ) : PhysicalSum G A.team (μ-p.profile.θ i) (dimT p.side i) true s (fun z=>p.off z i) (p.head i) ( ApplyMM (φ.native B) (Stripped A.team) A w ) X ↔ pre φ p A μ w i s=X:= Track.finite_bridge _ (dimT_even p.side i) _ (tFees A w) _ _ _ _ _ _

lemma treeCost {V:Fleet.Terrify W I} (h:Dial.CutoffM (φ.native B) w p μ true A V)(hx:V ∅=0): MF=V ∧ μF=ordZ V:= by
    have hf(i:I): pre φ p A μ w i = fun s=> bury i s V:= funext fun s=> (raw φ p A μ w i s _).mp (h i s)
    constructor ; swap; · exact funext fun s=> funext fun n=> funext fun i=> congr_fun (congr_fun ( hf i ) s) n
    let Y(i:I):= fun s n=> V s n i; funext s n i; unfold connected; rw [hf i,(show MS.Puff.Log.Meter Trunk ( marked W ) (fun s=> bury i s V)=Y i from (MS.Puff.Log.recheck _ _ _ (show Y i∈ allIndex _ _ from fun _ _ _ _=> Submodule.mem_top) (Tide.pointed _ hx i)))] -- ambiguous _

structure certified : Prop where
    scale : ∃ Y: Rake.Dance G I W, νS MF Y
    dial : νC MF
    unique : ∀ V:Fleet.Terrify W I, Dial.CutoffM (φ.native B) w p μ true A V → V ∅=0 → V=MF
    pre_log : μF= ordZ MF

lemma certifies (X:Dial.Uses p l μ)(H:∃ V:Fleet.Terrify W I,νC V)(Hp:∃ Z Y, νS Z Y): certified b φ p A μ w l:= by
    rcases H with ⟨ V,hV⟩; rcases Hp with ⟨ Q,Y,hY⟩
    have hF:MF=V:= (treeCost φ p A μ w hV.cost hV.init).1
    have he: Dial.CutoffM (φ.native B) w p μ true A Q:= fun i s=> (X.reality i) ▸ hY.native i s
    exact ⟨⟨ Y, (treeCost φ p A μ w he hY.empty).1.symm ▸ hY ⟩, hF.symm ▸ hV, fun _ h hx=> (treeCost φ p A μ w h hx).1.symm, hF.symm ▸ (treeCost φ p A μ w hV.cost hV.init).2 ⟩

lemma clears (X:Dial.Uses p l μ)(h:G.Simple)(H:TaylorOKM b (φ.native B) A): certified b φ p A μ w l:= certifies b φ p A μ w l X (Dial.check_tM b (φ.native B) w p H X h true) (Tide.calledM w p.off X.total X.reality X.upright X.super h X.clear X.wind X.knit H true)

omit [LinearOrder W] in
def AllProfiles (A:Land.Prescription B) : Prop:= TaylorOKM b (φ.native B) A ∧ ∀ (W I:Type) [LinearOrder W] (p:Dial.Trial I W)(μ:ℝ)(w:W→Label B)(l:Filter I), Uses p l μ → certified b φ p A μ w l
-- rate at test-array positions incl diagonal limit. Doesn't assert rate replacing moving by limiting points unless continuity supplies. each i set geometry, only i order/h independent cocycle.
lemma accuracy(c:AllProfiles b φ A)(X: Uses p l μ)(s:Finset W)(n:ℕ): PeakT.twin l p.profile mildG ( (↧A MF) s n ) (fun i=>Dial.book b w μ (testP p i) s n) ∧
  PeakT.twin l p.profile mildG ( (↧A μF) s n ) (fun i=>Dial.tour b w μ (testP p i) s n) := by obtain ⟨_,hq,_,hz⟩:=@c.2 W I _ p μ w l X; exact ⟨hq.ready _ _, hz.symm ▸ hq.bouquet s n⟩
section profile
variable [Fintype W]
lemma on_positions (c:AllProfiles b φ A)(h: Uses p l μ){x:W→Tone.QP} (he: Injective x)(ht:Tendsto (testP p) l (𝓝 x)) (s:Finset W)(n:ℕ): Tendsto ( (↧A MF) s n ) l (𝓝 ( Dial.book b w μ x s n )) ∧ Tendsto ( (↧A μF) s n ) l (𝓝 ( Dial.tour b w μ x s n )):= by
    obtain hc:= @c.2 W I _ p μ w l h; rw [hc.pre_log]; exact Dial.profile_tM b (φ.native B) w p hc.dial h he ht s n
end profile
lemma ceases {p:Land.Prescription B} (hS:TaylorOKM b (φ.native B) p) (H:G.Simple): AllProfiles b φ p:= by
    exact ⟨ hS,fun W I _ Q x f l he=> clears b φ Q p x f l he H hS ⟩
lemma fixes {p:Land.Prescription B} (h:G.Simple)(hc: TaylorOK b (φ.simple B) p): ∃ q, AllProfiles b φ q ∧ q.team=p.team := by
    obtain ⟨T,hT,h⟩:= Land.fixedClockM h b (φ.native B) p.team hc.bulk
    exact ⟨ T,ceases b φ hT (by assumption),h ⟩

theorem throughTide (h:G.Simple) : ∃ p q, Matched.AllProfiles b (φ.diction B) p ∧ AllProfiles b φ q ∧ q.team=p.team := by
    obtain ⟨p,H⟩:= Matched.allProfiles_remove b (φ.diction B) h
    obtain ⟨q,G,h⟩:= fixes b φ h H.1; exact ⟨p,q,H,G,h⟩
theorem throughDial (h:G.Simple) : ∃ p q, Matched.AllProfiles b (φ.diction B) p ∧ AllProfiles b φ q ∧ q.team=p.team := by
    obtain ⟨p,H⟩:= Matched.allProfiles_rake b (φ.diction B) h
    obtain ⟨q,G,h⟩:= fixes b φ h H.1; exact ⟨p,q,H,G,h⟩
end YM.FVA2.MixedStory
