import YM.OPE.Compatible.Hull.Poem
import YM.Extra.MULTISOURCE_BOUNDS.Columns
import YM.OPE.Compatible.LevelX.Fond
import YM.OPE.Compatible.Hull.Nook
import YM.OPE.Compatible.Hull.Spoon
import YM.OPE.Compatible.Hull.Bud
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Source Labels Source.Drops
section
open Beamer Next.Foundations Extra.Multi MvPolynomial
variable {d:ℕ}{H:Hol G}{R:Rep G n} {X: Labels.Frame G d} (T:SectionData X)(v:Coefficient X n)(W:Snap G d)(A:ℂ→L[ℝ]ℝ)
structure Pet (a u c:ℝ):Prop where
     form : v.Format o H R
     cap : v.remBound o R u c
     columns : ∀ i:X.Index, R.p.Regular (T.footprint o) (T.places (Pi.single i 1) o) ∧ R.p.supBounds o (T.footprint o) (T.places (Pi.single i 1) o) (a * R.p.threshold ^(X.grades i).2)
structure Shoo (n':ℕ) (x:Finset ℕ):Prop where
     supports : ∀ i∈ x,v.support i ⊆ Spindle.patch n' o
     stemmed : T.stencil ⊆ Lattice.box n'
noncomputable def GroveV (x:Finset ℕ)(R:Rep G n) := T.places (X.scaled R.p.threshold⁻¹ v.x) o + ∑ i∈x,v.regular i
variable {x:Finset ℕ}{a c B:ℝ}
lemma Coal (p:Pet o T v a c B (H:=H) (R:=R))(S:Shoo o T v b x)(h:R.p.order ≥ k)(hp:Widen R.p b) : Acceptance o R.p k (GroveV o T v x R) b (a*X.coeffSize v.x+B):=by
      obtain ⟨hf,⟨w,p',hw,hp',hh,hkey,⟨e,he,hE⟩,V⟩,ht⟩:=p; let Z:= T.footprint o; have hz: Z ⊆ Spindle.patch b o:=by rw [patch_eq]; exact image_subset_image S.stemmed
      obtain ⟨hP,hA⟩:=BasisCost.analytic T R.p v.x o ht; obtain ⟨Hq,hB⟩:=regular_bound_sum x v.regular e (fun i hi=>⟨regular_larger (hf.smooth i) (S.supports i hi), bound_larger (hE i) (S.supports i hi)⟩); have hu:=bound_add (regular_larger hP hz) Hq (bound_larger hA hz) hB; have hi: (∑ i∈x,e i) ≤ B:= ((Finset.sum_le_sum fun i _=> R.p.loMass _ _ (hE i).1).trans ( (he.2.1.sum_le_tsum _ fun i _=> he.1 i).trans he.2.2)).trans ((le_add_of_nonneg_right hp').trans hh); have hY:= add_le_add_right hi (a*X.coeffSize v.x); exact ⟨h,hp,regular_add (regular_larger hP hz) Hq, hu.1.trans (by linarith),fun i h v hi hh=> (hu.2 i h v hi hh).trans (by linarith)⟩ -- sums order
abbrev OpticZ {X:Labels.Frame G d}(z:X.Coeff)(W:Snap G d):ℂ:= MvPolynomial.aeval (Spindle.kp d W) (LiftMark.Tariffs.expose X z) -- kp path
set_option maxHeartbeats 200000 in
lemma viewCost (R:Rep G n)(W:Snap G d)(u:X.Coeff)(hT:T.Sound H) (S:T.stencil ⊆ Lattice.box b)(hm:2*(4*b+1)<n.val):
     let v:= (fun t:ℝ=> T.places u o (south H o W R.p.threshold t)); ContDiffAt ℝ d v 0 ∧ Spindle.evaluate_ray v d=OpticZ (X:=X) (X.scaled R.p.threshold u) W:=by
           intro z; let x:=R.p.threshold • W; let V:=X.coords.symm u; let p:= expand d x
           have hk: z= fun t=> T.evaluate u (H.links d p t):=by
                funext t; apply T.cylinder_local; intro i hi ht; exact content (b:=b) (by omega) H p d t i (S hi) (S ht)
           obtain ⟨hv,hA,ht⟩:=hT.projects u p; rw [hk]; refine ⟨hv,?_⟩
           let f := fun r=> Labels.read (scaleJet p r) V.val; let Y:= fun r=> aeval (Spindle.kp d (Spindle.flash x r)) (LiftMark.Tariffs.expose X u); let F:= fun r=>T.evaluate u (H.links d p r); change Spindle.evaluate_ray F d=_; have hs:ContDiffAt ℝ (d:ℕ) F 0:=hv; have h₀:ContDiffAt ℝ d f 0:=hA; have he:∀ i ≤ d, iteratedDeriv i F 0=iteratedDeriv i f 0:=ht; rw [Spindle.trill d hs h₀ (Spindle.depth hs h₀ he),show f=Y from _root_.funext (fun i=> Spindle.rewrites V (scaleJet p i))]; calc
             Spindle.evaluate_ray Y d= MvPolynomial.aeval (Spindle.kp d x) _ := Spindle.ray_stamp x (LiftMark.Tariffs.expose X u)
             _ = MvPolynomial.aeval (Spindle.kp d x) (LiftMark.Tariffs.expose X u) := congr_arg (MvPolynomial.aeval (Spindle.kp d x)) (Spindle.circle V)
             _ = _ := Spindle.clothes X W _ u
lemma coreG (R:Rep G n)(hT:T.Sound H)(U:Config G n): T.places (X.scaled R.p.threshold⁻¹ v.x) o U=v.x 0+ T.places (X.scaled R.p.threshold⁻¹ (X.core v.x)) o U:=by
     have hp:v.x=v.x 0 • X.e0+X.core v.x:=by ext1 i; by_cases h:i=0 <;> simp [h,Labels.Frame.e0,Labels.Frame.core,Function.update]
     nth_rw 1[hp]; unfold SectionData.places; rw [map_add,map_smul,Labels.Frame.scaled_unit,T.eval_linear.map_add,T.eval_linear.map_smul,hT.unit]; simp
end
end YM.OPE.Spells
