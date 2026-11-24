import YM.OPE.Compatible.Spa.Gum
/-!
# Phase shifts and leading coordinates in `Dross`

`ideaΓ` identifies the phase coordinates of the shift `WaneZ`. Given a complement
of `Ghost` and the stated flag, cutoff, and lifting hypotheses, `Spark` proves that
`WaneZ` preserves `Dross`, that a coordinate of an element of `Dross` belongs to
`Ghost` when its earlier coordinates vanish, and that every `Ghost` element occurs
as the phase-zero coordinate of an element of `Dross`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
local notation "G*"=> Gauge
local notation "N!"=> Dross Hp Z a
-- The degree-zero projection and its behavior under the phase shift.
variable (he:e<l+1)
abbrev Prime (e:ℕ)(he:e<l+1): Z.Mint e →ₗ[ℝ] Bead G l e:= (LinearMap.proj 0).comp (Z.BoxesΦ e he).toLinearMap
lemma ideaΓ : Horb (E:= ↥(Fruition Z.station (lapPrice P.L e))) (F:=Bead G l e) (Prime Z e he) (Z.WaneZ e he).toLinearMap (Z.BoxesΦ e he):=by
       refine ⟨fun _=>rfl,fun v=>?_⟩; funext i;fin_cases i
       · exact rise0 Z he v
       · exact riseΦ Z he v 0 1 rfl
       exact riseΦ Z he v 1 2 rfl
variable {a} {Y:M→ℝ}{V:(j:M)→Alps K T i (Y j)}{p₁:Clip}{hq:1 ≤ Y}{U: Z.Ω M Y}{hp:4 ≤ i} (T':Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(hw:l*l≤ τ 0)(hx:∀ j,(V j).clip=p₁)(L:Lance X)
private lemma constant_flag (Y' : M → Submodule ℝ (Tracts G d τ)) (host : HostE e 1 U Y')
    (x : Bead G l e) (hg : x ∈ Ghost G l e) (hm : Nonempty M) :
    ∃ (t : M) (z : U.flag e t), z.val ∈ Y' t ∧ tag D₀ e z.val = x := by
  obtain ⟨z, _, hrow⟩ := host (e+1) (fun _ => x) (wealthC x) (fun _ => ⟨hg, fun j hj => by omega⟩)
  obtain ⟨t⟩ := hm
  exact ⟨t, z t, (hrow t).1, (hrow t).2.2⟩

include T' in
private lemma spark_shift (x : Mint Z e) (hp : x ∈ Dross Hp Z a e) :
    WaneZ Z e he x ∈ Dross Hp Z a e :=
  budgetRide Hp Z a T'.dimD T'.cap T'.vol he x hp

include T' L in
private lemma spark_leading (p : Mint Z e) (hp : p ∈ Dross Hp Z a e) (i : Phase)
    (hprefix : ∀ j : Phase, j < i → BoxesΦ Z e he p j = 0) : BoxesΦ Z e he p i ∈ Ghost G l e :=
  Nem Hp Z a he T'.dimD T'.cap T'.vol p i hp ((bridgeV Z i.val i.isLt.le he p).2 hprefix) L

include T' in
private lemma spark_read (t : M) (z : U.flag e t)
    (hz : z.val ∈ Sapling (V := V) (H := H) (hs := hs) (hq := hq) (hp := hp) (a := a) (D₀ := D₀) t) :
    U.read e he t z ∈ Dross Hp Z a e :=
  stockMe (Z := Z) (V := V) (V' := U) (hv := le_trans zero_le_one hq) Hp T' t z hz

include hw hx T' L
private lemma spark_toll (x : Bead G l e) (hg : x ∈ Ghost G l e) (hm : Nonempty M) :
    ∃ p ∈ Dross Hp Z a e, x = BoxesΦ Z e he p 0 := by
  let Y' := Sapling (V := V) (H := H) (hs := hs) (hq := hq) (hp := hp) (a := a) (D₀ := D₀)
  have hhost : HostE e 1 U Y' :=
    (arsenal (Z := Z) (U := U) (V := V) (hq := hq) Hp T' L hx hw (zero_le_one : (0 : M → ℝ) ≤ 1) he).1
  obtain ⟨t, z, hz, htag⟩ := constant_flag (Z := Z) (U := U) Y' hhost x hg hm
  exact ⟨U.read e he t z, spark_read (Z := Z) (U := U) (V := V) (a := a) (hq := hq) Hp he T' t z hz,
    htag.symm.trans (discU (Z := Z) (U := U) he t z).symm⟩

set_option maxHeartbeats 200000 in
lemma Spark (A:Submodule ℝ (Bead G l e))(h:IsCompl (Ghost G l e) A) (_h:Nonempty M): Flank (E:= ↥(Fruition Z.station (lapPrice P.L e))) (F:=Bead G l e) (BoxesΦ Z e he) (WaneZ Z e he).toLinearMap (Ghost G l e) A (Dross Hp Z a e):=by
  exact ⟨h, spark_shift (Z := Z) (V := V) (U := U) (a := a) (hq := hq) Hp he T',
    spark_leading (Z := Z) (V := V) (U := U) (a := a) (hq := hq) Hp he T' L,
    fun x hg => spark_toll (Z := Z) (V := V) (U := U) (a := a) (hq := hq) Hp he T' hw hx L x hg _h⟩
omit hw hx T' L
end YM.OPE.Stroke
