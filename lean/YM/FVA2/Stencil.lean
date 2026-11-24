import YM.FVA2.Absolutes
import YM.FVA2.Cone

/-!
# Wilson input stencils

Relatively general; covers all the glyph `stamp`. Doesn't by itself specify
engineering dimension, gauge completion or scheme; expect those hypotheses on actual
applications. Leading rank at least `degree` before external g^{-degree}.
Can store translations or real-stencil data without continuity hypothesis away from 1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian
open PertExtension PertExtension.Orb
open Matrix FVA2.Ends ArrayMap Substitute Lag
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side}
local notation "A"=> Choice.allLetters G n
local notation "W"=> rootedVertex G n
local notation "V"=> fullRoot G n
local notation "Ω"=> enterF G n
local notation "C"=> Wilson.Config G n
local notation "χ"=> Inversion.χ G n
local notation "S"=> BackRoot (n:=n) (G:=G)
local notation "X"=> Bplane G n

lemma at_least {F I:Type}[Fintype F] (U:Matrix F I ℂ)(r:ℤ)(A':Raw F ℂ)(h:From A' r): From (ξ[U] A') r:= by
  intro l hl; rw [← enough l (F:=ξ[U] A') rfl, ← in_rank, show mask (l.length:ℤ) A'=0 from ?_,map_zero]; rfl
  funext i; by_cases he:(i.length:ℤ)=l.length; exact (enough i he).trans (h i (by omega)); exact strange _ he

structure Unscaled (G:Gauge) where
   degree : ℕ
   stencil : Dot G Cover
   bottom : From stencil.val degree
   stencilVal (n:Side) : Wilson.Config G n → ℝ
   invariant n : Native.Chart.OpenGauge (Native.Chart.drive n) (stencilVal n)
   chart n : germ (stencilVal n ∘ Ends.exp_A)
   usesStencil n : enters n stencil= reads (stencilVal n ∘ Ends.exp_A)

def shiftPort (i:Cover)(n:Side) (x:Edge (Site n)):Edge (Site n):=(wrap n i+x.1,x.2)
namespace Unscaled
variable (F: Unscaled G) (x: Cover)

def carries (n:Side) (w:Wilson.Config G n) : ℝ:= F.stencilVal n (w ∘ shiftPort x n)
omit F in
def linkA (n:Side) (G:Gauge) (x:Cover) : FullX G n→L[ℝ] FullX G n:= Sew.pull (shiftPort x n)
local notation "f"=> F.carries x n
local notation "v"=> F.degree

lemma carries_invariant : Native.Chart.OpenGauge (Native.Chart.drive n) (F.carries x n) := by
    intro h t; unfold carries; rw [show Native.Chart.siteGauge _ _ _ ∘ shiftPort x n = Native.Chart.siteGauge (Native.Chart.drive n) (fun i=> h (wrap n x+i)) (t ∘ shiftPort x n) from ?_]; exact F.invariant n _ _
    funext i; unfold Native.Chart.siteGauge; simp [Native.Chart.endRail,shiftPort, add_assoc]
lemma takes : GaugeInvariant f := fun g p=> by
    rw [show Lattice.gauge g p= Native.Chart.siteGauge (Native.Chart.drive n) g⁻¹ p from funext fun e=> by unfold Lattice.gauge Native.Chart.siteGauge; simp; rfl]; exact F.carries_invariant x ..
lemma shift_links : f ∘ Ends.exp_A = (F.stencilVal n ∘ Ends.exp_A) ∘ linkA n G x:= rfl
lemma marks_grid : germ (f ∘ Ends.exp_A):= by
   rw [shift_links]; exact (show ContDiffAt ℝ ω _ (linkA n G x 0) from by rw [map_zero]; exact F.chart n).comp 0 (linkA n G x).contDiff.contDiffAt

lemma shifted_arity : landV (G:=G) (n:=n) x F.stencil = ink tangentVec (f ∘ Ends.exp_A) := by
   have h : shown n F.stencil=Sew.art id (F.stencilVal n ∘ Ends.exp_A):= by
      apply Subtype.ext; apply (F.usesStencil n).trans; rw [Sew.pooled id (F.chart n)]; rfl
   unfold landV; change ξ[χ] (shown n (Lab.Shift x F.stencil)).val = _
   rw [ show shown n (Lab.Shift x F.stencil) = Lab.Shift (wrap n x) (shown n F.stencil) from trans_shift .., h]; unfold Lab.Shift; rw [ Sew.map_sec, Sew.pooled _ (F.chart n)]; exact stencil_ink (f∘ Ends.exp_A) (F.marks_grid x)

lemma at_shift : From (ink (tangentVec (P:=Site n)) (f∘ Ends.exp_A)) (↑v) := by
   rw [← shifted_arity]; apply at_least; have he : From (enters n F.stencil) v:= from_pass n F.bottom
   intro l hl; rw [← enough l (F:= enters n (Lab.Shift x F.stencil)) rfl];
   change mask _ (shown n (Lab.Shift x F.stencil)).val l=_; rw [show shown n (Lab.Shift x F.stencil) = Lab.Shift _ (shown n F.stencil) from trans_shift ..];
   unfold Lab.Shift transport; rw [← mask_s,← mod_ferry];
   have hv : model (l.length:ℤ) (shown n F.stencil) =0:= by
      apply Subtype.ext; ext k; by_cases h':(k.length:ℤ)=l.length; exact (enough k h').trans (he k (by omega)); exact strange _ h'
   rw [hv,map_zero]; rfl

abbrev imageMark (n:Side) := F.carries x n ∘ liftLinks
abbrev nativeMark (n:Side) := F.imageMark x n ∘ Ends.exp_A
local notation "Fₛ"=> F.nativeMark x n
lemma turn_F : Fₛ=(f∘ Ends.exp_A) ∘ Ω:= by
    funext i; change f (liftLinks _) = f (Ends.exp_A _); rw [show Ω i=incl G n i from rfl,lifted_physical]
lemma native_smooth : germ Fₛ:= by
    rw [turn_F]; exact (show ContDiffAt ℝ ω _ (Ω 0) from by rw [map_zero]; exact F.marks_grid x).comp 0 (Ω).contDiff.contDiffAt
lemma root_degree : From (ink (tangentVec (P:=Vert n)) Fₛ) v := by
    rw [turn_F, ← ghost_ink Ω Ω tallyY _ (F.marks_grid x)]; apply at_least; exact F.at_shift x
lemma native_invariant : (root n).invariant (F.imageMark x n):= root_inv f (fun g _ p=> F.takes x g p)
lemma pull_F : ξ[S] (landV x F.stencil) = ξ[X] (ink tangentVec Fₛ) := by
   rw [shifted_arity, BackRoot, Bplane,ghost_ink _ _ _ _ (F.marks_grid x),ghost_ink _ _ _ _ (F.native_smooth x),turn_F]; rfl
lemma levels_charge (i:ℕ): landV x (levels v F.stencil i) = rankLevel v (ink (tangentVec (P:=Site n)) (f ∘ Ends.exp_A)) i:= by
   rw [ ← shifted_arity ]; unfold rankLevel levels landV Lab.Shift transport
   rw [mod_ferry, ← in_rank]; exact congr_arg (ξ[χ]) (enterShim (b:=false) n (i+v))
lemma levels_pull (i:ℕ): ξ[S] (landV x (levels v F.stencil i))=
   ξ[X] (rankLevel v (ink tangentVec Fₛ) i):= by
   rw [ levels_charge, ← shifted_arity ]; unfold rankLevel; rw [in_rank,in_rank,F.pull_F x]
end Unscaled

end YM.FVA2.Inversion
