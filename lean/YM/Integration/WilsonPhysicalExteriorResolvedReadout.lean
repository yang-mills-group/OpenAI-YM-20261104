import YM.Integration.WilsonPhysicalExteriorResolvedCutoff
import YM.FVAAlt2.Shop.Match

/-! The separated mixed geometric source now reads the *actual* deposited
finite lattice table and the independently selected continuum prescription.
No external convergence at a fixed configuration is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolvedReadout
open YM.MS MS.Dial WilsonPhysicalExteriorUVStory WilsonPhysicalExteriorResolvedCutoff
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet -- order
open Lattice
open scoped Topology ContDiff
open Vane PeakT Program Menus Swirl Swirl.Near
open Native Wilsonian

section
variable {I W:Type} {P:Geo I} {x:Position W I}
theorem geometry (hx:Resolved P x) (i:I) : Function.Injective (pointI x i) := by
  intro v w he
  by_contra hn
  obtain ⟨C,_,hh⟩:=hx v w hn
  have hi:=hh i
  change x v i=x w i at he
  rw [he,sub_self,norm_zero,mul_zero] at hi
  exact (not_le_of_gt (Real.exp_pos _)) hi

structure Domain (T:Trial I W)(l:Filter I)(μ:ℝ):Prop where
  total : Reach T.profile T.off
  knit : Resolved T.profile (Fleet.info T.off)
  reality i : T.profile.η i=μ-T.profile.θ i
  upright : Tendsto T.profile.θ l atTop
  super : Super l T.side T.profile.θ
  clear : Clearance T.side T.head
  wind : Vista.width T.side T.head
end

section
variable {I W E:Type} {G:Gauge} [LinearOrder W]
variable {B:Local.Physical.Deck G}{M:Booked B}(A:MS_Data G M)(u:W→Rake.Label B)
variable {U:Rake.Dance G I W}{x:Position W I}(v:ℝ)
variable (h:Resolved (frameF I v) x)(ht:DOrd M (frameF I v) A u x U)(p:I)
include h ht
theorem raw (s:Finset W)(k:ℕ): U s k p=spine A u v (pointI x p) s k ():= by
    have he:= valid_copy u ht (fun (_:Unit)=>p) (Q:=frameF Unit v) (fun _=>rfl)
    obtain hp:spine A u v (pointI x p)=copy (fun (_:Unit)=>p) U:= perfect (pin A u v (geometry h p)) he
    rw [hp]; rfl

theorem book_value (F:Finset W)(n:ℕ): Fleet.toZ U F n p=book A u v (pointI x p) F n:= by
    unfold Fleet.toZ book Vane.blade
    rw [raw A u v h ht p]

theorem tour_value (F:Finset W)(n:ℕ): ordZ (Fleet.toZ U) F n p=tour A u v (pointI x p) F n := by
    have he : (fun s k=>Fleet.toZ U s k p)=book A u v (pointI x p):=funext fun s=>funext fun k=>book_value A u v h ht p s k
    unfold ordZ bury tour
    rw [he]
end

section
variable {W I:Type} {μ:ℝ}{n:ℕ}[LinearOrder W] {l:Filter I}
variable {G:Gauge}{B: Deck G}{M:Booked B}(S:MS_Data G M)(φ: RichBook B)(p:W→Label B)
   (T:Trial I W){A:Prescription B}
theorem coherent (h:TaylorOKPl S φ A)(U:Domain T l μ)(hp:G.Simple)(b:Bool): ∃ V:Terrify W I,coherentPl M S φ p T μ b A l V:= by
    obtain ⟨ Z,Y,hY⟩:= WilsonPhysicalExteriorResolvedCutoff.physical p T.off U.total U.reality U.upright U.super hp U.clear U.wind U.knit h b; have hv:=presented (μ:=μ) T.off U.knit; have hh(s:Finset W)(n:ℕ): Fleet.toZ Y s n=(fun i=> book S p μ ( testP T i ) s n):= funext fun i=> book_value S p μ hv hY.scheme i s n;
    refine ⟨Z,hY.empty,fun i s=>?_,fun i u=> hh i u ▸ ( hY.compares i u ).1,fun i t=>?_ ⟩; exact U.reality i ▸ hY.native i s; rw [ ← show ordZ ( Fleet.toZ Y ) i t=(fun s=> tour S p μ ( testP T s ) i t) from funext fun s=> tour_value S p μ hv hY.scheme s i t ]; exact ( hY.compares i t|>.2 ) -- parser
end

section
open YM.FVAAlt2 YM.FVAAlt2.Lobby
open Function Finset Filter Topology Lattice Labels Source
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Plane
open MS.Land MS.Lifting MS.Local.Physical MS.Book.Convolve MS.Native.Studio MS.Native.Paint MS.Native.Wilsonian
open MS.Puff MS.Puff.Mom MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Dial MS.Tide MS.Swirl MS.Swirl.Near MS.Fleet MS.Rake MS.Vista MS.Vane
open PowerSeries (C coeff)
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation Precision Pert.Orb Billing
open scoped Topology BigOperators ContDiff PowerSeries
variable {G:Gauge}{d k:ℕ}{n:Side}{B:Deck G}{L:Frames G}{H:Hol G}
variable {W:Type} [LinearOrder W](D:ChartRatio G)(R:Lobby.Registry L H)
variable [Fintype W]
variable (K:MS.Land.Prescription B)(y:ℝ)(p:W→Rake.Label B)
local notation "pf"=> YM.FVAAlt2.Lobby.Table R B
local notation "g"=> Rake.Label.h∘p
local notation "PSc"=> PowerSeries ℂ
local notation "TC"=> redo K.team
local notation "∂"=> univ (α:=W)

variable {A:Type}{T:Trial A W}{l:Filter A}{μ:ℝ}{M:Booked B}(S:MS_Data G M){X:Terrify W A}

omit [LinearOrder W] [Fintype W] in
theorem admissible (h: Domain T l μ) : ∀ᶠ i in l,Admissible (dimT T.side i) := by
 filter_upwards [h.upright.eventually_ge_atTop 4,h.super (1:ℝ)] with i he ht
 rw [one_mul] at ht; have hb:= Real.log_le_sub_one_of_pos (Vista.δ_p T.side i)
 refine ⟨ ?_,?b ⟩; case b=> rw [dimT,cap_val]; simp
 suffices hw : (4:ℝ) ≤ Vista.tickA T.side i by exact_mod_cast hw
 linarith

theorem measured (h:LocalRatio D) (hu:Domain T l μ) (hg:G.Simple)
    (hk:TaylorOKPl S pf K) (k:ℕ) :
    PeakT.twin l T.profile mildG (evaluateR D R K p T μ k)
      (fun i=>tour S p μ (testP T i) Finset.univ k) := by
  obtain ⟨U,hU⟩:=coherent S pf p T hk hu hg true
  obtain ⟨hs,hv⟩:=hU.bouquet univ k
  refine ⟨hs,PeakT.fromζ hv ?_⟩
  filter_upwards [admissible hu] with i hi
  rw [Pi.sub_apply,Pi.sub_apply,Lobby.distanceT D R K p S h hU i k hi]
end

end YM.Integration.WilsonPhysicalExteriorResolvedReadout
