import YM.RGComparison.Core16.Astage.Landing
/-!
# To the separated-profile OPE

Sufficient producer ticket on *fixed physical horizon off-shell* of candidate comparison lift.
Prove the MOMENT (raw normalized hierarchical reading against the finite detectors printed here)
vs match approximation U_m M, before any inversion to the filtered pivots. In doing so no OPE
coefficient comparison is an input. Here show then the QFTA spatial estimate needed by `measured`
hc (provided input charge in our Quota, as for `Axle.option` lift on all stages). The OPE packet is
the reference basis one on every phase & all labels, `Reader` from `Exhibit`. Tests here are NOT
already b-horizon Reader or an IR reg. Must be provided from the actual product/capture/re-closure
calculation with the adequate cumulative accuracy, *including its subextraction limit*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Panel
open Function Filter Real Metric Set MeasureTheory OPE Labels Table Orbits Axle
open Ward Extraction Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
section routes
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (T:Final C f S)(d:ℕ) 
include T in
lemma senses (p:Exterior C.book)(v:S.Field d) : S.spectra d v p= upon S d 0 (bearing p) (fields S p) v:=by
    let z:=S.representative d v; let q:C.book.Token:=⟨d,z⟩; let u:= bearing p; have hi:= bearing_clear p
    let x:Orbits.Labels S (expo p):=fields S p; let A:Unit→S.Field d:=sole v
    let f:=observe S (beside (sole (0:E4)) u); let s:= S.classTokens; have h₁ := T.room.kernel.laws.toSymmetric; let K:= Fin p.n
    have hs : S.spectra d v p= observe S (beside (sole (0:E4)) u) (beside (sole q) p.letter):=by
       rw [← (S.rep d v)]
       have hh:= Prescription.one_test (S:=S) d p (S.representative d v) T.room.kernel
       symm; simpa only [Prescription.reading,sub_zero,if_pos (bearing_clear _)] using hh -- defeq?
    rw [hs]
    change observe S _ _ = whole S (sole _) (A: Labels S (fun _:Unit=>d)) u x; rw [whole_observed];
    rw [observe_exact (S:=S) S _ h₁ (fun _=>le_rfl) hi, observe_exact (S:=S) S _ h₁ (fun _=>le_rfl) hi]
    have he(i:Unit⊕K): S.classTokens (beside (sole q) p.letter i)=s (beside (names (A: Labels S fun _:Unit=>d)) (names x) i):=by
       rcases i with i|i
       · rfl
       change (⟨_,S.project _ (p.letter i).snd⟩:S.Tag)=⟨(p.letter i).fst,S.project _ (S.representative _ _)⟩; rw [S.rep]; rfl
    apply congr_arg (S.useAt S _); funext i; exact he _

def slates (R:Reader T.sector.derivatives T.sector.turns T.room.kernel.spin) : Finset (Exterior C.book):=
    (bands T.sector.derivatives d).biUnion fun i=> (R.port.sheet i).support
set_option quotPrecheck false
variable (R:Reader T.sector.derivatives T.sector.turns T.room.kernel.spin){ι:Type}{l:Filter ι}{u:ι→ℝ}{b:ℝ}
local notation "K!"=> bands T.sector.derivatives d
lemma detects (v:ι→ S.Field d)(ht:Tendsto u l atTop)
    (h:∀ p∈ slates T d R,RateLE l u (fun i=>upon S d 0 (bearing p) (fields S p) (v i)) b): RateLE l u v b:=by
    let R' := R.port; have hp(p)(hi:p∈K!):RateLE l u (fun i=>R.port.test p d (v i)) b:=by
       unfold Prescription.test; simp_rw [computes,senses T]; apply RateLE.sum ht; intro j hj; exact ((RateLE.const (R.port.sheet p j) ht).mul (h j (Finset.mem_biUnion.mpr ⟨p,hi,hj⟩))).mono (by simp)
    exact (RateLE.sum (S:=K!) ht (fun j hj=> ((hp j hj).smul (RateLE.const (R.port.loaded j d) ht)).mono (show b+0 ≤ _ from by rw [add_zero]))).congr (Eventually.of_forall fun i=> (R.spans d).rebuilds _)
lemma clearX {I:Type}[Fintype I]{x:I→E4}(h:Injective (beside (sole (0:E4)) x))(hp:Tendsto u l atTop):
    Kept l u 0 (fun _=> x) ∧ Intervals l u 0 (fun _=>sole 0) (fun _ => x):=by
    let f (_ : ι) : Unit⊕I→ E4:=beside (sole (0:E4)) x
    have hv:Kept l u 0 (fun _ : ι=>beside (sole (0:E4)) x):=by
       intro b hb; let g i:= f i; let w:Tendsto (fun i=>exp (-b*u i)) l (𝓝 0):= Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by linarith) hp); refine eventually_all.mpr (fun j=>eventually_all.mpr (fun k=>?_));
       by_cases he:j=k; · exact Eventually.of_forall (fun _ hi=> (hi he).elim)
       exact (w.eventually (gt_mem_nhds (norm_sub_pos_iff.mpr (h.ne he)))).mono fun _ he _=> he
    constructor
    · exact fun b hb=>(hv b hb).mono fun i he j k hk=> he (.inr j) (.inr k) (Sum.inr_injective.ne hk)
    exact fun b hb=>(hv b hb).mono fun i he j k => he (Sum.inl j) (Sum.inr k) (by simp)
end routes

-- Exact match condition for the before-integrals limits at resolution f. $ζ$ positive.
-- price at REAL hierarchical reference. Can pass any stronger spatial gain too.
set_option maxHeartbeats 580000 in
lemma wing {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (T:Final C f S) (H:Services C f S) (R:Reader T.sector.derivatives T.sector.turns T.room.kernel.spin)
    {φ:Filter (ℕ×ℕ)} [φ.NeBot](hf:φ≤ f.fuse)
    {I K:Type} [Fintype I]{ι:Type}{l:Filter ι}[l.NeBot] [MeasurableSpace K][Nonempty K]
    {m:ι→ℕ}(ht:Tendsto m l atTop) (u:ℕ){d:I→ℕ}(A:ι→ Labels S d) (hA:∀ j, Axle.Crew φ (κ:=l) (m:=m) (fun i=>A i j))
    {x:ι→K→I→E4} {p:ι→K→ℂ} {μ:ι→Measure K}
    (hx:∀ v:ι→ K, enveloped l (ruler C m) 1 (fun i=>x i (v i)) 0 ∧ Kept l (ruler C m) 1 (fun i=>x i (v i)))
    (ha:∀ᶠ i in l, Integrable (p i) (μ i))(hs: RateLE l (ruler C m) (fun i=>∫ j, ‖p i j‖ ∂μ i) 0)
    (hv:∀ᶠ i in l, Integrable (fun j=> p i j • R.packet u (x i j) (A i) 0) (μ i))
    (hW:∀ a∈slates T u R,∀ᶠ i in l, Integrable (fun j=> p i j * Orbits.whole S (x i j) (A i) (bearing a) (fields S a)) (μ i))
    {ζ:ℝ}(hz:ζ≤1)(v:ι→S.Field u)
    (he:∀ a∈slates T u R, RateLE l (ruler C m) (fun i=> sales (μ i) (p i) (x i) S (A i) (bearing a) (fields S a)- upon S u 0 (bearing a) (fields S a) (v i)) (-(u+ζ :ℝ))) :
       RateLE l (ruler C m) (fun i=> sampled T R u (μ i) (p i) (x i) 0 (A i) - v i) (-(u:ℝ)-ζ):=by
    have hk:=large_s C ht
    refine detects T u R _ hk (fun a ha'=>?_)
    let w:= fields S a; let y:ι→ Fin a.n→E4:= fun _=> bearing a
    have hy:=clearX (bearing_clear a) hk; have hB:= true_balance T H R hf ht u A hA w (x:=x) (p:=p) (μ:=μ) (y:=y) (o:=0) (fun _=>none) hx ha hs hv hy.2 hy.1 (hW a ha') -- hx defeq 0 map etc.
    let X i:= sales (μ i) (p i) (x i) S (A i) (bearing a) w; let W i:= sampled T R u (μ i) (p i) (x i) 0 (A i); let V:= upon S u 0 (bearing a) w
    apply (((he a ha').mono (b:=-(u:ℝ)-ζ) (by linarith)).sub (hB.mono (by linarith)) hk).congr
    apply Eventually.of_forall; intro i; change X i-V (v i)-(X i-V (W i))=V _; rw [map_sub]; abel
end YM.RGComparison.Core16.Astage.Panel
