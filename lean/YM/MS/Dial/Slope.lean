import YM.MS.Dial.Frame
/-! Use continuum functions at actual points. independ of support and sampling. Continuity proven at every compact separated shape. Contact output left zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Fleet Puff Engine Actors Puff.Mom
open PeakT -- ordZ
open Vane
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{r:ℕ}[LinearOrder W]{l:Filter I}
variable {B:Deck G}{M:Booked B}(A:MS_Data G M)(u:W→Rake.Label B)
def spine (μ:ℝ)(x:W→ QP): Rake.Dance G Unit W:= open Classical in if H: ∃ Y,DOrd M (frameF Unit μ) A u (fun p _=> x p) Y then H.choose else 0
lemma pin (μ:ℝ){x:W→QP}(hp:Injective x): DOrd M (frameF Unit μ) A u (fun p _=>x p) (spine A u μ x):= by
    unfold spine; split_ifs with h; exact h.choose_spec; suffices he: Mesh (frameF Unit μ) (fun p (_:Unit)=>x p) from False.elim ( h (formal ( builder A he u )) );
    intro i j hi; have he:0<‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hp.ne hi)); refine ⟨⟨_,he,fun i=>?_⟩,⟨_,he,fun i=>?_⟩⟩ <;> simp [frameF,roots]
abbrev pointI (x:Position W I)(i:I): W→QP:= fun t=>x t i
variable {U:Rake.Dance G I W}{F:Finset W}{x:Position W I}(v:ℝ)
local notation "R"=> frameF I v
variable ( h: Mesh (frameF I v) x)(ht: DOrd M (frameF I v) A u x U) (p:I)
include h
lemma detailI : Injective (pointI x p):= by intro a b he; exact Milk.PlainI _ h _ ( congr_arg Theater.fixF he ) -- p meta
include ht
lemma PointI (s:Finset W)(k:ℕ): U s k p=spine A u v (pointI x p) s k ():= by
    have he:= valid_copy u ht (fun (_:Unit)=>p) ( Q:=frameF Unit v ) (fun i=>rfl); obtain hp:spine A u v (pointI x p)= copy (fun (_:Unit)=>p) U:= perfect (pin A u v (detailI v h p)) he; rw [hp]; rfl -- detail implicit
abbrev book (t:ℝ)(i:W→ QP): Finset W→ T ℂ:= fun p j=> Vane.blade (spine A u t i p j) ()
abbrev tour (t:ℝ)(i:W→QP) (t':Finset W):= Puff.Mom.bouquet ( book A u t i ) t'
lemma Point_t (F:Finset W) (n:ℕ): Fleet.toZ U F n p=book A u v (pointI x p) F n:= by unfold Fleet.toZ book Vane.blade; rw [PointI A u v h ht p]; -- maybe too many params S etc
lemma shape_f (F:Finset W)(n:ℕ): ordZ (Fleet.toZ U) F n p=tour A u v (pointI x p) F n := by
    have he : ( fun s k=> Fleet.toZ U s k p)=book A u v (pointI x p):= funext fun s=> funext fun k=> Point_t A u v h ht p s k; unfold ordZ bury tour; rw [he]
variable [l.IsCountablyGenerated](hp:∀ w,tend l p (x w))
include hp
lemma Symbol (n:ℕ): tend l p (fun i=> book A u v (pointI x i) F n):= by
    obtain hZ|hZ:=F.eq_empty_or_nonempty; · subst F; simp_rw [ ← Point_t A u v h ht,Fleet.toZ,ht.1, Pi.zero_apply,show Vane.blade (0:Glade G I)=0 from funext (fun i=> (allow_zero i).2 ) ]; exact tendsto_const_nhds -- erases defeq issue
    simp_rw [← Point_t A u v h ht]; exact owed u h ht hp ( reports u h ht hZ n )
lemma Rail (s:Finset W)(n:ℕ): tend l p (fun i=> tour A u v (pointI x i) s n):= by
    let S(i:I):= book A u v (pointI x i); exact Accord.select ( l:=l ) (f:=S) (v:=S p) ( fun i k=> Symbol A u v h ht p hp k ) _ _ -- argument order
-- Continuity w.r.t points nearby. Finite W. Need ℝ-norm product Pi instances.Prop.Test.μ const.
end YM.MS.Dial
