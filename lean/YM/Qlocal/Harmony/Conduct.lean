import YM.Qlocal.Harmony.Mould
/-!
# Applying individual path polymer jets to tests on finite regulator

Multiplication in coupling order here. No uniformity in regulator mass in these convergence
arguments. The Stanza `Album.Health` is the mass-*independent* coat.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony
open Function Finset Filter Push Push.AbsoluteSums
open Lattice MeasureTheory Wilson Pressure RG Gauge
open Quipu Quipu.Sonnet
open Marker Stationary ConnectedActivityE6 ConnectedActivityE6.Blaze Extra.Iteration Push.Uniform
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {V ι:Type} [DecidableEq V] {R:Census V} {G:Gauge} {s:Senses R}
    {n r m j k:ℕ} {c:Side}
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Conductor
open Vase Album
variable {a C:ℝ} (Z:Album ι s G n) (h:Z.Health a C) -- fix
    (ha: 0<a) (p:ι→Prop) (o:V→Site c) (t:ℕ)
    (T:E→ Config G c){y:E}(ht:Weather T y)
-- preserve entire Hear predicate when specializing proof, not approximating only a center.
noncomputable abbrev solo (A:Vase s G n)(o:V→ Site c)(t:ℕ)
    : Config G c→ℝ := if Bay.Hears A.stage o then A.read (o (Sonnet.root s)) t else 0
include ht in
lemma value (A:Vase s G n) : ContDiffAt ℝ ω (solo A o t ∘ T) y:= by
 unfold solo; split
 next h=>
    rw [show (A.read (o (Sonnet.root s)) t ∘ T)=Complex.reCLM ∘ ((A.swatch (o (Sonnet.root s)) t) ∘ Work.F02.physical ∘ T) from ?_]; swap; · funext v; rw [Function.comp_apply]; exact ((congr_arg Complex.re (real_bill (A) (o (Sonnet.root s)) (T v) t)).trans (Complex.ofReal_re _)).symm
    exact Complex.reCLM.contDiff.contDiffAt.comp _ (((A.reign (o (Sonnet.root s)) t|>.restrict_scalars ℝ).contDiffAt.comp _ (Work.F02.physical_contDiffAt ht)))
 next => exact contDiffAt_const

-- need specialized because `if` curried vs unbundled conflicting
lemma utt (x:ι) : readout (fun i=> p i ∧ Bay.Hears (Z i).stage o) Z (o (Sonnet.root s)) t x=if p x then solo (Z x) o t else 0:= by
 unfold solo readout; split_ifs with hx hy hz; rfl -- multiple goals 
 all_goals first | rfl | tauto
set_option quotPrecheck false
local notation "P"=> (fun i=> p i ∧ Bay.Hears (Z i).stage o)
local notation "O"=> o (Sonnet.root s)
-- Weather needed implicit with p.Y.Doc Semantic
include ht ha h
lemma winter : ContDiffAt ℝ ω (Album.picture p Z o t ∘ T) y:= Album.winter _ Z _ t h ha T ht
lemma printed (L:E→ℝ)(hl:ContDiffAt ℝ ω L y)(k:ℕ) :
    HasSum (fun j=> iteratedFDeriv ℝ k (L * (readout P Z (o (Sonnet.root s)) t j ∘ T)) y)
      (iteratedFDeriv ℝ k (L * (Album.picture p Z o t ∘ T)) y):= by
 obtain ⟨u,H⟩:= Album.habitat T ht k
 have hz :∀ᶠ y' in 𝓝 y,Weather T y':= eventually_all.mpr fun i=> (ht i).eventually (by simp)
 obtain ⟨d,hd,hV⟩:= Brush.neighborhood y (hl.of_le (le_top (a:=(↑k: WithTop ℕ∞))))
 obtain ⟨b,hb,hB⟩:= Metric.eventually_nhds_iff_ball.mp (H.and ((hl.eventually (by simp)).and (hV.and hz)))
 let B:= Metric.ball y b; have h₀: y∈B:= Metric.mem_ball_self hb
 let X(i:ι):= L*(readout P Z O t i ∘ T)
 let f (i:ι):=Vase.capita G n t k u a * (Z i).fare a
 let g(i:ι):=2^k*1*d*f i
 have he(z:E)(he:z∈B)(i:ι): Allows k (X i) z (g i):= Allows.bilinear (ContinuousLinearMap.mul ℝ ℝ)
    (show Allows k L z d from ⟨(hB _ he).2.1,(Brush.offer.mp (hB _ he).2.2.1).inside⟩)
    (show Allows k (Album.readout P Z (O) t i ∘ T) z (f i) from
      ⟨Album.jobs _ _ _ _ h ha T (hB _ he).2.2.2 i,(Brush.offer.1 (Album.paths _ _ _ _ h ha T (hB _ he).1 i)).inside⟩)
    (ContinuousLinearMap.opNorm_mul_le ..)
 have hg:Summable g:=(h.2.1.mul_left _).mul_left _
 have hh : L*(Album.picture p Z o t ∘ T) = fun i=> ∑' j,X j i:=by funext z; exact (tsum_mul_left (a:=L z) (f:=fun i=> Album.readout P Z O t i (T z))).symm
 change HasSum (fun j=>iteratedFDeriv ℝ k (X j) y) (iteratedFDeriv ℝ k (L* (Album.picture p Z o t ∘ T)) y)
 rw [hh,iterated_at_sum Metric.isOpen_ball (convex_ball y b|>.isPreconnected) hg (fun i z hx=>he z hx i) h₀ k le_rfl]
 exact (Summable.of_norm_bounded hg (fun i=> (he y h₀ i).norm_le k le_rfl)).hasSum
lemma attendance (L:E→ℝ)(hl:ContDiffAt ℝ ω L y)(k:ℕ) :
    HasSum (fun j=> if p j then iteratedFDeriv ℝ k (L * (solo (Z j) o t ∘ T)) y else 0)
      (iteratedFDeriv ℝ k (L * (Album.picture p Z o t ∘ T)) y):= by
 refine (printed _ h ha p o t T ht L hl k).congr_fun fun b=>?_ ; rw [utt]; split; rfl
 next hb=> rw [show (0: Config G c→ℝ) ∘ T= 0 from rfl,mul_zero]; simp
end Conductor
end YM.Qlocal.Harmony
