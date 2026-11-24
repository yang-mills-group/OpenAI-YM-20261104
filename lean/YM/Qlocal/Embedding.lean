import YM.Qlocal.Caption
import YM.Qlocal.Discount
import YM.Overlay.Bill
/-!
Exact quiet of any Peak using the SOLD histories. Makes the norm visible and
establishes actual vacuum identities on all stages, even normalized readout
(of course not a qlocal scalar matching estimate). Supplies existence of data
for analytic operations with integrals of each poly coordinate, never used
for a marked comparison budget and not charged here. `total` moments NOT
provided, that's the separate holder. ALL terms even global captions.
 Logs available w*rho same carrier.V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Publishing.Peak
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {o:V→Site n}{e b r A B X Y k σ C Λ:ℝ} {w:V→ℝ}{c:R.Mode→ℝ} {T:Taste Ω o P R}
variable (hw:∀ i,0<w i)
section geom
include hw
private lemma rents {α:ι→Support n}{q:ι→R.Mode}{f:ι→ℝ} (p:BudgetPoint) (h:∀ i, 0 ≤ f i) (hV:∀ i,0 < f i→ ∀ j∈(q i).val, o j ∈ α i)
    (he:Ac.Hit α p.B (fun i=>Poly.toll w (q i)*f i) p.supportExponent A) (j:V) : SumBudget (fun i=> if j∈ (q i).val then Poly.toll w (q i)*p.mass (α i) (f i) else 0) A:= by
 refine budget_mono (he (o j)) (fun i=> ?_) (fun i=> ?_)
 · split; exact mul_nonneg (Poly.worth hw _).le (mul_nonneg (Real.exp_nonneg _) (h _)); rfl
 split
 next ht=>
   rcases eq_or_lt_of_le (h i) with hx|hx
   · rw [BudgetPoint.mass,← hx,mul_zero,mul_zero]; exact (he _).1 _
   rw [if_pos (hV i hx j ht)]; unfold BudgetPoint.mass; ring_nf; rfl
 next ht=> exact (he _).1 _

-- raw Radial on actual data when not relative normalize. useful for any projection
lemma rotor (h:Peak P o T (fun i=>Poly.toll w i) P.p.supportExponent A B) (x:Ω) : (T.leaf x).contents.Radial w 0 A B 1:=by
 obtain ⟨f,hf,hV,hQ⟩:=h.regular; obtain ⟨z,hz,hT,hZ,hK⟩:=h.forced; let hp:=(h.active x).articles;
 refine ⟨hw,fun i=> ?_,zero_lt_one,⟨f,fun i=> ⟨hf _,fun j hj=> hV _ i _ (hp.pins i j hj)⟩, rents (o:=o) hw _ hf (fun i _ j hj=> (congr_fun T.root j) ▸ (show T.menu.origins j∈T.menu.branch i from hp.pins i j hj)) hQ ⟩,⟨z,fun i j=> ⟨hz _, fun U=>hT _ (i,j) U⟩,?_⟩⟩
 · rw [show (T.leaf x).contents.units i=0 from h.units x i,norm_zero,mul_zero]
 rw [mul_one]; exact rents (o:=o) hw _ hz (fun i=>hZ i.1 i.2) hK

variable (h:Peak P o T c P.p.supportExponent A B)(hp:∀ i,0 < c i) (x:Ω) [Nonempty Ω]
include h hp
lemma radial : ∃ a b,Peak P o T (fun i=>Poly.toll w i) P.p.supportExponent a b:= by
 obtain ⟨p,hp'⟩:= Finite.bddAbove_range (fun i:R.Mode=>Poly.toll w i/c i); refine ⟨_,_,Peak.transfer (fun i=>(Poly.worth hw i).le) (show 0 ≤ p+|p| from (by linarith only [neg_le_abs p])) h (fun i hi=> (div_le_iff₀ (hp i)).mp (((show Poly.toll w i/c i≤p from hp' ⟨i,rfl⟩)).trans (le_add_of_nonneg_right (abs_nonneg _))))⟩
omit hw
variable [Fintype V] (hv:P.Lawful σ C Λ b r)
include hv
lemma same (U:Config G n): ((T.leaf x).density U).part R.quiet=(P.eval U:ℂ):=by
 obtain ⟨a,b,hS⟩:=h.radial (w:=fun _=>1) (fun _=>zero_lt_one) hp -- argument order?
 rw [StageArt.detached P.p.exponent_pos.le h x hp, Poly.quiet_mul, Poly.pass_part _ (StageArt.mute P.p.exponent_pos.le h x hp), one_mul]; exact Bands.same _ (h.active x).articles (rotor (fun _=>zero_lt_one) hS x) hv.labels U
-- Integration of each component.H Need integrable FULL poly.
lemma soluble (hβ:0 ≤ P.beta) : Integrable (T.leaf x).contents.density (prior G n):= by
 obtain ⟨a,b,hS⟩:=h.radial (w:=fun _=>1) (fun _=>zero_lt_one) hp
 suffices H : Integrable (fun y:Config G n=>fun j:R.Mode=> ((T.leaf x).contents.density y).part j) (prior G n) from H
 exact integrable_pi_iff.2 (fun i=> (Overlay.Bands.material _ (h.active x).articles (rotor (fun _=>zero_lt_one) hS x) hv hβ i).1)
-- name for pass.Algebra.
lemma density_integrable (hβ:0≤P.beta) : Integrable (T.leaf x).density (prior G n):=by
 rw [funext (StageArt.detached P.p.exponent_pos.le h x hp)]
 let L : Poly R→ₗ[ℂ] Poly R:={ toFun := ((Poly.pass (T.leaf x).captions.chord)*·), map_add':= fun i j=>mul_add .., map_smul':=fun i j=>mul_smul_comm .. }
 exact (L.restrictScalars ℝ).toContinuousLinearMap.integrable_comp (soluble h hp x hv hβ)
end geom
end YM.Qlocal.Publishing.Peak
