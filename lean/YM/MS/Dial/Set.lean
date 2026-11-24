import YM.MS.Dial.Loom
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
open Orbit Rake Tide Vista Lattice
variable {P:Geo I}
lemma unpose (p:Berth ( I:=I ) ( W:=W ))(h:Mesh (frameF I v) (lifted P p)): Mesh P ( Fleet.info p ):= by
    intro a b he; let X:=P.roots; have ht : ∀ i, 0<X i:= fun i=> exp_pos _; let q:= lifted P p; let V:= info p; have hp (i:I) : ‖( V a-V b ) i‖= X i * ‖( q a-q b ) i‖:= by rw [scaleF p i, norm_smul_of_nonneg (exp_pos _|>.le)]; unfold X roots; rw [ Real.exp_neg,← mul_assoc,mul_inv_cancel₀ (exp_pos _|>.ne'),one_mul ]
    obtain ⟨⟨C,hC,hP⟩,A,hA,hB⟩:= h a b he; simp only [ roots,frameF,Pi.zero_apply,exp_zero,mul_one ] at hB hP; refine ⟨ ⟨ C,hC,fun i=>?_⟩,⟨ A,hA,fun i=>?_⟩⟩; · exact le_trans ( Eq.le (hp i) ) ( ( mul_le_mul_of_nonneg_left (hP i) ( ht i|>.le ) ).trans_eq (mul_comm ..) )
    rw [ show ‖(info p a-info p b) i‖=_ from hp i ]; rw [ mul_comm A ]; exact mul_le_mul_of_nonneg_left (hB i) ( ht i|>.le )
-- exhaustion.Profile.Trial
structure Trial (I W:Type) where
    profile: Geo I
    side: I→ Lattice.Side
    off: Berth ( I:=I ) ( W:=W )
    head:I→ Cover
variable (T:Trial I W)
structure Uses (T:Trial I W)(l:Filter I)(η:ℝ): Prop where
    total: Profile T.profile T.off
    knit: Mesh T.profile ( Fleet.info T.off )
    reality i: T.profile.η i=η-T.profile.θ i
    upright:Tendsto T.profile.θ l atTop
    super: Super l T.side T.profile.θ
    clear: Clearance T.side T.head
    wind: Vista.width T.side T.head
abbrev testP (i:I): W→QP:= fun w=> lifted T.profile T.off w i
lemma micro (h:Mesh T.profile (info T.off)) : ∀ i, Injective (testP T i):= fun _=> detailI 0 (posed T.off h) _ -- namespace Field.
end YM.MS.Dial
