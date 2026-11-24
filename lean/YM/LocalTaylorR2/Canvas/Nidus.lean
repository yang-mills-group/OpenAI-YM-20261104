import YM.LocalTaylorR2.Canvas.Scenes

/-!
 # Family of spatial charts through Taylor tasks. Small AND measurable/
 all-probe smooth, and trustworthiness at priced sites.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Canvas
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {χ:Chi} {E :Type} [NormedAddCommGroup E] [ NormedSpace ℝ E] {x:E}{U : E → Config G c} {v d e : ℝ} {k : ℕ}

-- Capture *with* cutoff for all fields. No derivative of this choice.
structure Basecamp (G:Gauge) where
  R : ℝ
  B : ℝ
  log : Reliable G R B

def primary (G:Gauge):Basecamp G:= Classical.choice (by obtain ⟨g,r,hg,ht⟩:= reliable G; exact ⟨r,g,ht r hg le_rfl⟩)

def point (D : Basecamp G) (χ : Chi) (d : ℕ) (o : Site c) (V:Config G c) : Directions G c:=fun i=> if separation o i.1≤ d then cutLog χ D.R (pedestal o V i) else 0

-- Borel and gauge notes for individual books, throughout all volumes, j tested at E. Reliable.smooth adaptation for just j.
attribute [local instance] Gauge.frobInner
lemma Basecamp.smooth (D: Basecamp G) {u : E→ G.El}(h:ContDiffAt ℝ (↑k) (fun y=> G.mat (u y)) x): ContDiffAt ℝ k (fun y=> cutLog χ D.R (u y)) x:=by
  have hv : ContDiffAt ℝ (↑k) (fun y => χ.innerShare D.R (G.chord (u y))) x := by
    unfold Chi.innerShare; simp_rw [Gauge.chord,div_pow]
    have he := (contDiff_norm_sq ℝ).contDiffAt.comp (f:=fun y => G.mat (u y)-1) x (h.sub contDiffAt_const)
    exact (χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp x ((he.div_const _).div_const _)
  by_cases he : G.chord (u x)≤ 2*D.R
  · exact hv.smul (((D.log.patch _ he).of_le le_top).comp x (g:=G.plog) (f:=fun y=> G.mat (u y)) h)
  have ht : ContinuousAt u x := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr h.continuousAt
  refine (contDiffAt_const (c:=(0:G.Color))).congr_of_eventuallyEq ?_
  filter_upwards [(G.continuous_chord.continuousAt.comp ht).eventually (lt_mem_nhds (lt_of_not_ge he))] with y hy
  have hu : χ.innerShare D.R (G.chord (u y))=0 := by by_contra hg; exact (χ.chosen_lt _ _ D.log.down hg).not_ge hy.le
  rw [cutLog,hu,zero_smul]

lemma beacon (k : ℕ) (d : ℝ)(i : Bond c)(u:ℕ) (h : separation o i.1 + 1≤ u) (he : Mode U x k d) : let g:= royalty G; let v:= 4*(u:ℝ)*(d*g)
    Brush k g (v*g+(d*g+v)) (fun y=> G.mat (pedestal o (U y) i)) x :=by
  intro g v; let f z y := carrier o (U y) z
  have ht (i : Site c) (hi : separation o i≤u) : Brush k g v (G.mat ∘ f i) x:=by
    apply (tour (carriage o i) o he.pos he.atLink).climb le_rfl; unfold v
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (SliceRows.mileage o i).trans (Nat.mul_le_mul_left 4 hi)) (mul_nonneg he.pos (zero_le_one.trans (royalty_ge _)))
  have hy:= (next_le (r:=separation o i.1) le_rfl).trans h
  have h₁:= ht i.1 (by omega); have h₂:= reverse (ht _ hy)
  simp_rw [pedestal,Lattice.gauge, mul_assoc, G.mat_mul]; have hp : max 1 g ≤ g:= max_le (royalty_ge G) le_rfl
  apply links h₁ (g:=fun v=> G.mat (U v i)*_) ?_ g hp; exact links (he.atLink i) h₂ g hp

lemma highway (G:Gauge) (L:Side): Rate G L 0 (fun s=> reserve (40*radiusB s)):= by
  let B x:=40*(radiusB x:ℝ)
  have h: Rate G L 0 B:= Rate.radius_price.mul_left 40
  unfold reserve; push_cast
  let p:= Rate.const (L:=L) (G:=G) 1
  have hf:= Rate.add (((((h.mul_left 2).add p).mul_left 4).mul_left 2)) p
  simpa only [zero_mul,zero_add] using! (hf.mul ((((((h.add p).mul_left 2).add p).pow 5).mul_left 16).mul_right _))

-- d≤32B. In this proof 40B cleaners; may be stronger than the physical scope must sometimes pay. Consume after 200B.
lemma Basecamp.tenant (G:Gauge) (L : Side) (P:Teller G)(J: Basecamp G)(k : ℕ) {v : ℝ→ℝ}(V : Rate G L (-(1/2)) v) (hv : ∀ᶠ x in atTop,0≤v x): ∃ p : ℝ→ℝ, Rate G L (-(1/2)) p ∧
    ∀ᶠ s in atTop, 0<p s ∧ ∀ (c f: Side) (S:StepData c f)(T:Tube G S), S.patch.L=L→ Room P S T s→ ∀ d:ℕ,d≤ 32*radiusB s → ∀ (E :Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V:E→ Config G c) x (χ:Chi) (o:Site c), Mode V x k (v s)→ Clean (V x) s o (40*radiusB s+1) → Brush k (p s) 1 (fun y=> point J χ d o (V y)) x ∧
      ∀ᶠ y in 𝓝 x, AgreeNear id o d (pedestal o (V y)) (increment 1 (point J χ d o (V y))) :=by
  obtain ⟨M,R,hR⟩ := cleanly G k 1 zero_lt_one
  let g:= royalty G; let t x:= 2*Pressure.fiery G x L; let B x:= reserve (40* radiusB x)*t x; let u x:= 40*(radiusB x:ℝ); let w x := 4*u x*(v x*g); let A x:= w x*g+(v x*g+w x)
  let a x:= (1+g)*A x; let K := (k.factorial:ℝ)*M
  have hB:Rate G L (-(1/2)) B := by simpa only [zero_add] using! ((highway G L).mul (Rate.flame.mul_left 2))
  have hw:Rate G L (-(1/2)) w := by simpa only [zero_add] using! (((Rate.radius_price.mul_left 40).mul_left 4).mul (V.mul_right g))
  have ha:Rate G L (-(1/2)) a := ((hw.mul_right g).add ((V.mul_right g).add hw)).mul_left _
  let e x := Pressure.fiery G x L+(J.B*|B x|+K*a x); have h := J.log; have hx:= h.down
  refine ⟨e,Rate.flame.add (((hB.compare (v:=fun x=> |B x|) (Eventually.of_forall fun z=> (abs_abs _).le)).mul_left J.B).add (ha.mul_left K)),?_⟩
  filter_upwards [hv, hB.below (by norm_num) (J.R/2) (half_pos hx), ha.below (by norm_num) 1 zero_lt_one,
    (hB.mul_left G.colorScale).below (by norm_num) R hR.pos, (Work.E09.betaF_growth G L).eventually_gt_atTop 0] with s hp hΨ hZ hΩ hS
  have he:0≤a s:=by unfold a A w u; have hh:= royalty_ge G; change 1≤g at hh; positivity
  have hZ':0<Pressure.fiery G s L:= Work.E09.temp_pos hS
  have hb : 0≤K := mul_nonneg (Nat.cast_nonneg _) hR.value.le; have hu := h.price
  have hE:0< e s:=by unfold e; positivity
  refine ⟨hE,?_⟩; intro c f S T hL hP d hd E _ _ V x χ o hm hh
  let p i:= pedestal o (V i); let D i':= point J χ d o (V i')
  have hf (i : Bond c) (hj: separation o i.1 ≤ d) : Brush k (e s) 1 (fun y=> D y i) x ∧ ∀ᶠ y in 𝓝 x, p y i=increment 1 (D y) i:= by
    have hi: separation o i.1 + 1 ≤ 40*radiusB s:= by have hh:=hP.sight; omega
    have hG : Brush k g (A s) (fun y=> G.mat (p y i)) x:= by convert! beacon (o:=o) k (v s) i (40*radiusB s) hi hm using 1; unfold A w u; push_cast; rfl
    have hy : G.chord (p x i) ≤ B s:= draw _ i (by have hh:=hP.buys; omega) hi hh (by unfold t; positivity) (by unfold t; rw [← hL]; exact hP.temperatures)
    have hF : ‖G.mat (p x i)-1‖ ≤ R:=by rw [← chord_dist]; exact (mul_le_mul_of_nonneg_left hy G.colorScale_pos.le).trans ((le_abs_self _).trans hΩ)
    have hT : G.chord (p x i) < J.R := by have hb := (le_abs_self _).trans hΨ; linarith
    have hh : ∀ᶠ y in 𝓝 x,G.chord (p y i) < J.R :=by
      exact (((hG.smooth.continuousAt.sub_const 1).norm.div_const G.colorScale)).eventually (gt_mem_nhds hT)
    let U y:= G.plog (G.mat (p y i)); have hQ y : G.chord (p y i)<J.R → D y i= U y:=fun hy=> by unfold D point; rw [if_pos ‹separation o i.1 ≤ d›]; exact h.kept χ _ hy.le
    constructor
    · have hk:Brush k K (a s) U x:= (hG.pine (hR.sound _ hF))
      suffices hh' : Brush k (e s) 1 U x from hh'.shimmy (hh.mono fun y => hQ y)
      apply Brush.offer.mpr; refine ⟨hk.smooth,fun k hk'=>?_⟩
      have h₀ : J.B*|B s| ≤ e s:= (le_add_of_nonneg_right (mul_nonneg hb he)).trans (le_add_of_nonneg_left hZ'.le)
      rcases k with _|k
      · unfold normJ; rw [norm_iteratedFDeriv_zero]
        exact ((h.cap _ (show G.chord (p x i)≤2*J.R by linarith))).trans ((mul_le_mul_of_nonneg_left (hy.trans (le_abs_self _)) hu.le).trans h₀)
      apply (hk.order _ hk').trans
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he ((le_abs_self _).trans hZ) (by omega : 1 ≤ k+1)) hb).trans
        (by rw [pow_one]; unfold e; nlinarith only [hZ',mul_nonneg hu.le (abs_nonneg (B s))])
    filter_upwards [hh] with y hy; rw [increment, hQ y hy,h.right (p y i) (show G.chord _ ≤ 2*J.R by linarith),Pi.one_apply,mul_one]
  refine ⟨Brush.fold zero_le_one hE.le (fun i=>?_),?_⟩
  · by_cases hi:separation o i.1 ≤d; · exact (hf i hi).1
    exact Brush.zi (Eventually.of_forall fun y=>if_neg hi) hE.le zero_le_one
  let I:= univ.filter fun i:Bond c=> separation o i.1 ≤d
  filter_upwards [(Finset.eventually_all _).mpr (fun i (hi:i ∈ I)=> (hf i (mem_filter.mp hi).2).2)] with y hy i hi; exact hy _ (mem_filter.mpr ⟨mem_univ _, hi⟩)
end YM.LocalTaylorR2.Canvas
