import YM.UniformConstruction.ReadoutCompat.OriginalPilots
/-!
 Wiring proportional anomaly on single rail without even uniform measured germs. Keep sparse.
 Mixed sum orientation FIRST argument, spectator at second uncentered (manifold magnetic).
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace MeasureTheory Next.UVStress Climb Cells
open PhysicalNext.Repeat.Legato Metric Lattice
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{S:Table C.book}{f: Extraction.Order}{F: Final C f S}{u:Filter (ℕ×ℕ)}{B:Lenses.Mantle F u}{L:Layout F} (E:Services C f S) {s:Extraction.Sequence}
set_option quotPrecheck false
local notation "M"=> Maxwell.freeTable C.labels
local notation "P"=> portal L
local notation "θ"=> role C
local notation "W"=> interval B s
variable (h:Stands L B s)(Z:Ledger L)(fx:Flick C.path.levels) {x:Points 2}

abbrev blue (C:Family G)(i:Axis): Fin 2 → Free C 4:=![Trace.metric0 C.labels i timeAxis,φS C]
abbrev toss (L:Layout F)(i:Axis):= sail L (d:=fun _=> 4) (blue C i)
abbrev red (C:Family G): Fin 2 → Free C 4:=fun _=>φS C
abbrev flare (L:Layout F) := sail L (d:=fun _=>4) (red C)
abbrev hope (L:Layout F) (r:ℝ):= Points.gradient 0 timeAxis (flare L r)
abbrev needle (i:Axis)(L:Layout F)(r:ℝ):= Points.gradient 0 i (toss L i r)
def spool (L:Layout F) (x:Points 2) (r:ℝ) := ∑ i:Axis, needle i L r (ay C x r)

lemma flash_now {y:Points 2}{r a d:ℝ}{k:ℂ}(hr:0<r)(hv:StressRay F (P r) r a d k)(hx:y∈conf _) : a • (∑ i:Axis, needle i L r y)+d • hope L r y=0:=by
    let w:=scalarRay P r
    have h:=Trace.divergence_system F P hv w (r•y) (Work.A05.smul_conf hr hx) timeAxis
    rw [Finset.smul_sum] at h
    change a • (∑ i:Axis,swipe r (tensorRay P r i timeAxis) w i y) + d • swipe r w w timeAxis y = 0 at h
    simp_rw [reduceSwipe _ _ hr _ F.room.kernel hx] at h
    unfold hope; rw [show flare L r=(fun x=>bilim (r•x) w w) from funext (fun x=>by unfold flare sail bilim; congr 1; funext j; fin_cases j <;> rfl)] -- inside hope
    have he(i:Axis): toss L i r= fun x=>bilim (r•x) (tensorRay P r i timeAxis) w:= by
        funext x; unfold toss sail bilim; congr 1; funext j; fin_cases j <;> rfl
    simp only [needle,he]; exact h

abbrev drum (C:Family G) (x:Points 2) (g:Axis→ℝ→Points 2→ℂ)(r:ℝ) := ∑ i:Axis, sightDiff C x 0 i (g i) r
include E Z h fx
lemma slid (hx:x∈conf _)(hm:Tendsto (fun r=> drum C x (toss L) r / (Z.g r:ℂ)^2) W (𝓝 ((anomalyCoefficient G/2) • bright C x))) : Tendsto (fun r=> spool L x r/(Z.g r:ℂ)^2) W (𝓝 ((anomalyCoefficient G/2) • bright C x)):=by
    have h' := (hm.sub (tendsto_finsetSum Finset.univ (fun (i:Axis) _ => flashed E h (d:=fun _=>4) (blue C i) Z fx hx 0 i))); simp only [Finset.sum_const_zero,sub_zero] at h'; exact h'.congr (fun r=>by simp only [toss,spool,needle,drum,← Finset.sum_div,Finset.sum_sub_distrib,sub_div]; abel) -- `← sum_div` correct?
private lemma angleRatio {a d:ℝ→ℝ}{k:ℝ→ℂ} (hp:x∈conf _)(he:bright C x≠0)(ha:∀ᶠ r in W,StressRay F (P r) r (a r) (d r) (k r))(hx:Tendsto (fun r=> spool L x r/(Z.g r:ℂ)^2) W (𝓝 ((anomalyCoefficient G/2) • bright C x))):
    Tendsto (fun r=>d r/Z.g r^2) W (𝓝 (-(anomalyCoefficient G/2))):=by
    let A r:= hope L r (ay C x r); have ht:Tendsto A W (𝓝 (bright C x)):= rides E h (d:=fun _=>4) (red C) Z fx hp 0 timeAxis
    have g: W ≤ home:=(homes B).comp s.cofinal
    have hs:Tendsto (fun r=> (↑(d r/Z.g r^2:ℝ):ℂ)) W (𝓝 (↑(-(anomalyCoefficient G/2):ℝ):ℂ)):=by
       rw [Complex.real_smul] at hx
       have hV:= (((Complex.continuous_ofReal.continuousAt.tendsto.comp (focusLimit E h ha)).neg.mul hx).div ht he)
       rw [Complex.ofReal_one, neg_one_mul,neg_div, mul_div_cancel_right₀ _ he, ← Complex.ofReal_neg] at hV
       apply hV.congr'; filter_upwards [ha,ht.eventually_ne he,positiveLength.filter_mono g,((reachesBase Z fx x).mono_left g).eventually ((conf_open _).mem_nhds hp)] with r hv hA hr hR
       have h:= flash_now hr hv (y:=ay C x r) hR; simp only [Complex.real_smul] at h
       have hh : (a r:ℂ)*spool L x r + (d r:ℂ)*A r=0 := h
       have hz : (↑(Z.g r):ℂ)≠0:=by exact_mod_cast (Z.positive r).ne'
       change (-(a r:ℂ)*_) / A r=_
       rw [Complex.ofReal_div,Complex.ofReal_pow]; field_simp; linear_combination -hh
    exact Complex.continuous_re.continuousAt.tendsto.comp hs

lemma aloft (hx:x∈conf _)(he:bright C x≠0)(hm:Tendsto (fun r=> drum C x (toss L) r / (Z.g r:ℂ)^2) W (𝓝 ((anomalyCoefficient G/2) • bright C x))) : SampleLog F W (theoryDensity G):=by
   have hb : W ≤ home:= (homes B).comp s.cofinal
   have hh: ∀ᶠ r in W,∃ a d k,StressRay F (P r) r a d k:= ((commands B L E h.pegs).aligned.mono fun i hi=> Trace.ray_of_alignment F P hi.some E.simpleGate).filter_mono hb
   rw [eventually_iff_exists_mem] at hh
   obtain ⟨V,hV,hU⟩:=hh; choose! a d k hA using hU
   have ha:∀ᶠ r in W,StressRay F (P r) r (a r) (d r) (k r):= mem_of_superset hV (fun x hx=>hA x hx)
   exact towardsTrace E Z hb ha (angleRatio E h Z fx hx he ha (slid E h Z fx hx hm)) (tendsto_map'_iff.mpr (pieces E h))
end YM.RG17
