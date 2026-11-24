import YM.LocalLTE.Fan.Vine
/-! Patch payments and unforced rare probability. Boots up support cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
-- angular ruler/rect
section
variable {ι :Type}[Fintype ι] [DecidableEq ι]{A:Matrix ι ι ℝ}
def cabinet (I:Finset ι)(r:ℝ):Set (Body (↥I)):= {z|∀ i, |z i| ≤ r}
omit [DecidableEq ι] [Fintype ι] in
lemma alive (I:Finset ι) r : MeasurableSet (cabinet I r):= by simp only [cabinet,Set.setOf_forall]; exact MeasurableSet.iInter fun i=> measurableSet_le (by fun_prop) measurable_const
omit [Fintype ι] in
lemma fur (I:Finset ι) {z:Body (↥I)} (hz: z∈cabinet I r)(hr:0≤r)(i:ι): |Pond.spill I z i|≤r:=by
  by_cases hi:i∈I
  · simpa only [Pond.spill,dif_pos hi] using! (@id _ (hz ⟨i,hi⟩): |z ⟨i,hi⟩|≤r)
  simp [Pond.spill,hi,hr]
omit [Fintype ι] in
lemma agenda (I:Finset ι){A:Matrix (↥I) (↥I) ℝ}(hp:A.PosDef) (h:∀ v:↥I→ℝ,dotProduct v (A *ᵥ v) ≤ W*dotProduct v v) (s:ℝ) : (Poll.sweep A).real (cabinet I s)ᶜ ≤ (I.card:ℝ)*(2*Real.exp (-s+W/2)):=by
  let Z (i:↥I):={ z:Body (↥I)|∀ j∈ ({i}:Finset (↥I)),s≤ |z j|}
  have he : (cabinet I s)ᶜ ⊆ ⋃ i∈ (univ:Finset (↥I)),Z i:=by
    intro k hk; simp only [cabinet,Set.mem_compl_iff,Set.mem_setOf_eq,not_forall,not_le] at hk
    obtain ⟨i,hi⟩:= hk; exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨mem_univ _,fun j hj=> ((mem_singleton.mp hj).symm ▸ hi.le)⟩⟩
  let Y:= Poll.sweep A
  have hV i : Y.real (Z i) ≤ 2*Real.exp (-s+W/2):= by
    have hp:=Poll.rectangle hp.posSemidef h {i} s 1 zero_le_one
    simpa only [Y,Z,neg_mul,one_mul,one_pow, mul_one,card_singleton,Nat.cast_one,pow_one] using! hp
  exact ((measureReal_mono he (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le ..)).trans ((sum_le_sum (fun i _=> hV i)).trans_eq (by simp))
end
lemma dozing {P:Teller G} (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(W:ℝ)(o:Target.Order G W){N:ℝ→ℝ}(h:Rate G L 0 N)(e:ℝ) : ∀ᶠ t in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)
      (F:Forest S.ratio)(X:Coat T F)(p:Disk G c)(I: Finset (Tubular f G))(μ α:ℝ)(R:Rep G f), Cash W t μ L Q o α T R → X.x=t → X.width=o.K → (timeΛ X p).manifest → (I.card:ℝ) ≤ N t →
     (Fan.pool I X p).real (cabinet I (postponement L t o))ᶜ ≤ betaF G t L ^e:=by
  let u:=tubularPrice G L; let K:= 1+payE o.eta o.gap o.ample u
  obtain ⟨r,hr⟩: ∃ r:ℝ,r<e:=exists_lt _
  let Z x:= Real.exp (-(postponement L x o)+K/2)
  have he:Rate G L r Z:= by
    apply (Rate.mul_right (Rate.monitor_cutoff (G:=G) (L:=L) (a:=r) (half_pos o.rare) (one_pos (α:=ℝ))) (Real.exp (K/2))).congr (Eventually.of_forall ?_) -- edit
    intro x; unfold Z; rw [Real.exp_add]; apply congr_arg₂ (·*·) ?_ rfl; apply congr_arg; unfold postponement; rw [Real.rpow_one]; ring
  refine ((h.mul (he.mul_left 2)) e (by simpa only [zero_add])).mono ?_
  intro x hx c f S T F X p I μ α R H ht hK hP hh
  let Y:=timeΛ X p; have ha:= (H.laws.data.localP F Y (show Y.x=x from ht) (show Y.width=o.K from hK) hP).sails
  let A:= Pond.circuit I Y.relating; have hA:A.PosDef := ha.fullC.submatrix Subtype.val_injective
  have hf:=Vine.admits Y ha.scale I ha.cap
  have hv q: dotProduct q (A *ᵥ q) ≤ K* dotProduct q q:= (le_abs_self _).trans (Control.top hf.relented hf.weather.1.le q) -- edit
  exact (agenda I hA hv (postponement L x o)).trans ((mul_le_mul_of_nonneg_right hh (mul_nonneg (by norm_num) (Real.exp_pos _).le)).trans ((le_abs_self _).trans hx))
end YM.LocalLTE.Fan
