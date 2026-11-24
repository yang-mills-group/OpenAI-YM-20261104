import YM.RG17.Magnet
import YM.RG17.Jackets
import YM.RG17.Teller
/-!
# Two-point tests for coupling calibration

`Beam` represents the uncentered grade-four moments by coefficient
functions continuous on separated configurations. `Emission` supplies a
signed estimate for the corresponding Wilson measurements on the given
history and regulator filter. `clearsOne` and `circles` use those inputs
at a generic two-point configuration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace MeasureTheory Next.UVStress Climb Cells Overlay Marker
open PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Final R.family f S}{u:Filter (ℕ×ℕ)}{B:Lenses.Mantle F u}{L:Layout F} (E:Services R.family f S) {s:Extraction.Sequence}
set_option quotPrecheck false
local notation "C"=> R.family
local notation "P"=> portal L
local notation "θ"=> role R.family
local notation "W"=> interval B s
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "K"=> wheel R.family

variable (Z:Ledger L)(h:Stands L B s)(fx:Flick R.family.path.levels) {x:Points 2}
abbrev podium (R:Run G):= ℝ→Fin 2→ R.family.label 4
-- The coefficient functions represent uncentered two-point moments.
structure Beam (A:Ports R.family)(p:ℕ) where
    light : Axis→ℕ→ℝ→Points 2→ℂ
    valid (r:ℝ)(hr:0<r)(i:Axis){j:ℕ}(hj:j≤p): ContinuousOn (light i j r) (conf _)
    trueAt (r:ℝ)(hr:0<r)(i:Axis){j:ℕ}(hj:j ≤ p)(ψ:Test 2): ψ.applyTo (light i j r)=A.moments (d:=fun _=> 4) (fun k=> Sum.inr (blue R.family i k)) j r ψ
abbrev aurora {A:Ports R.family}{p:ℕ}(b:Beam R A p) (i:Axis) := forecast Z p (b.light i)
abbrev vice {A:Ports R.family}{p:ℕ}(b:Beam R A p)(i:Axis) (r:ℝ)(x:Points 2) := standing L (fun j r=> b.light i j r x) p r
include h E fx
-- Wheel leaf pulled UP at this support. Estimate before total; allow sum
-- cancellations between each pair at identical table scales.
abbrev chem (v:podium R)(r:ℝ)(q:Fin 2→ «Cover»)(t:ℕ×ℕ) := ∫ U,pullDimes (p:=t.2) (N:=t.1) (shutter R L (fun _=>4) r t.1 t.2 (v r)) (rake R q r t) (Stock.final (Fin 2)) (wheel R.family r) U∂prior ..
variable {A: Ports R.family}{p:ℕ} (b:Beam R A p) (i:Axis)
-- same F port power on regulator. Charge δ for cancellation, not assume obtains for ordinary spatial correlations. Increase internal p at will (need signal then). Uses FULL outputs.
structure Emission (Z:Ledger L)(s:Extraction.Sequence)(b:Beam R A p) (x:Points 2)(i:Axis) : Prop where
    toll : ∃ (w:podium R)(j:ℕ)(a e:ℝ)(k:ℕ),0≤a ∧ 2<e ∧ (∀ᶠ r in interval B s, ∀ j':Fin 2,Paid (d:=fun _=>4) L r (w r) j' ≤ H (K r)^j ∧ master L 4 r (w r j')=portal L r (blue R.family i j')) ∧
       ∀ᶠ r in interval B s,∀ᶠ t in L.lens, let m:=keyMass R.family t.1 t.2; ‖chem (L:=L) R w r (nextRail R.family x 0 i r) t-chem (L:=L) R w r (baseRail R.family x r) t - (m:ℂ)*(vice (L:=L) R b i r (bee R.family x 0 i r) t - vice (L:=L) R b i r (ay R.family x r) t)‖ ≤ m*(role R.family r)*(a * ledgerCoupling L r t ^ e * Z.Λ r ^ k)
-- important: shape finite POINT predictions, not normalized integral over phases. To reach this using Gates physics must supply kernel from actual A construction + point evidence in addition to PSU Estimate.
set_option maxHeartbeats 800000 in
lemma clearsOne (hx:x∈generic 2)(hE:Emission (B:=B) R Z s b x i) : Tendsto (fun r=>(sightDiff C x 0 i (toss L i) r - sightDiff C x 0 i (aurora R Z b i) r)/(Z.g r:ℂ)^2) W (𝓝 0):=by
    have ht:W ≤ home:= (homes B).comp s.cofinal
    obtain ⟨w,j,a,e,k,ha,he,hT,hM⟩:= hE.toll
    let X:= baseRail R.family x; let Y:=nextRail C x 0 i
    obtain ⟨hp,H0⟩:= erectedNow R Z fx (fun _:Fin 2=>4) (blue C i) E h hT x X hx ((reachesBase Z fx x).mono_left ht)
    obtain ⟨hy,H1⟩:= erectedNow R Z fx (fun _:Fin 2=>4) (blue C i) E h hT x Y hx ((reachesNext Z fx x 0 i).mono_left ht)
    obtain ⟨q,_,hq⟩:= H0 0; obtain ⟨q',_,hr⟩:= H1 0
    let U:=aurora R Z b i; haveI : L.lens.NeBot:= L.notbot
    refine readoutAdmits Z W ht (by simpa using he) ⟨a,k,ha,?_⟩
    filter_upwards [hp,hq,hy,hr,hM,positiveLength.filter_mono ht] with r hp hq hy hr hM hR
    let y:=ay C x r; let z:= bee C x 0 i r; let δ:=θ r; have hd:0<δ:= div_pos (R.family.S.a_pos _) hR
    have hG:Tendsto (ledgerCoupling L r) L.lens (𝓝 (Z.g r)):= (Z.fuse_at r).mono_left L.certified
    have hh(c:Points 2) : Tendsto (vice R b i r (L:=L) c) L.lens (𝓝 (U r c)):=standingLimit Z ..
    let l₀:= receiptLine (L:=L) R (fun _=>4) (X r) (w r) r; let l₁:= receiptLine (L:=L) R (fun _=>4) (Y r) (w r) r
    have hf: ‖(toss L i r z - toss L i r y)-(U r z-U r y)‖ ≤ δ*(a * Z.g r ^ e* Z.Λ r^k):=by
       apply le_of_tendsto_of_tendsto (hy.sub hp|>.sub ((hh z).sub (hh y))|>.norm) (((hG.rpow_const (.inl (Z.positive r).ne')).const_mul a|>.mul_const _).const_mul δ)
       filter_upwards [hq,hr,hM] with t hs hu hh
       let m:= keyMass R.family t.1 t.2; have he:0 < m:=partition_pos _
       let c:ℂ:=↑m; have hc:c≠0:=Complex.ofReal_ne_zero.mpr he.ne'; let B':=vice (L:=L) R b i r z t - vice (L:=L) R b i r y t
       change ‖(l₁ t-l₀ t)- B'‖ ≤ δ*(a*ledgerCoupling L r t ^ e* Z.Λ r ^ k)
       rw [show l₁ t=chem (L:=L) R w r (Y r) t / c from hu.1,show l₀ t=chem (L:=L) R w r (X r) t/c from hs.1]
       apply le_of_mul_le_mul_left _ he
       have h (o g b e':ℂ)(u:ℝ) (he:o - g - c*b=e') (hh:‖e'‖ ≤ m*δ*u): m *‖o/c-g/c-b‖ ≤ m*(δ*u):=by
           rw [← mul_assoc m]; refine le_trans (le_of_eq ?_) hh; rw [← he,show m= ‖c‖ from (Complex.norm_real m|>.trans (Real.norm_of_nonneg (show 0 ≤ m from (partition_pos _).le))).symm, ← norm_mul]; congr 1; field_simp
       exact h _ _ _ _ _ rfl hh
    change ‖δ⁻¹ • (_-_) - δ⁻¹ • (_-_)‖ ≤ _
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hd).le]
    exact (mul_le_mul_of_nonneg_left hf (inv_pos.mpr hd).le).trans_eq (by rw [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul])

-- explicit obligations. Never supply Emission for another b. Signal
-- not smuggled into its computation. No claim estimates selected solve WilsonX.
theorem circles (hp:2 ≤ p) (hx:x∈generic 2)(he:bright C x≠0)(hE:∀ i,Emission (B:=B) R Z s b x i)(hf:Tendsto (fun r=> drum C x (aurora R Z b) r/(Z.g r:ℂ)^2) W (𝓝 ((anomalyCoefficient G/2) • bright C x))) : SampleLog F W (theoryDensity G) ∧ 0<theoryDensity G ∧ ∀ (m:ℕ)(U:F.action.operators.H →ₗᵢ[ℂ] Shell.Sum m),¬ Shell.Comparison F (meanExact F) U:=by
    have hq:= (tendsto_finsetSum Finset.univ fun i _=> clearsOne R E Z h fx b i hx (hE i)).add hf; simp only [Finset.sum_const_zero,zero_add] at hq
    have hv:= aloft E h Z fx (generic_conf _ hx) he (hq.congr fun r=>by simp only [drum,← Finset.sum_div, Finset.sum_sub_distrib,sub_div]; abel)
    have hp:=theoryDensity_pos E.simpleGate; exact ⟨hv,hp,fun _ U=> sampleClose _ E ((homes B).comp s.cofinal) hp U hv⟩
end YM.RG17
