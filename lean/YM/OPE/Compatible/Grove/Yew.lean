import YM.OPE.Compatible.Grove.Teak
/-! Paired path quadratic. Raw spectrum accepts any ℓ triangular. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
-- Pabeled indexed block. keep per-face series
abbrev Claw (R:PathData G)(p:PlaqAxes)(j:ℕ):= (R.row p j).2
abbrev FareU (R:PathData G)(p:PlaqAxes)(j:ℕ):= (R.row p j).1
def duetU (R:PathData G)(p:PlaqAxes)(s:Signed)(i:G.ColorIndex)(u:ℕ×ℕ):Chant G 2 := ![slotBeam (Claw R p u.1) s i,slotBeam (Claw R p u.2) s i]
def penny (R:PathData G)(p:PlaqAxes)(u:ℕ×ℕ):=FareU R p u.1*FareU R p u.2
lemma duoValue (R:PathData G)(p:PlaqAxes)(i:G.ColorIndex)(s:Signed)(a:ℕ) (b:ℕ)(V: CoverConfig G): verseX (duetU R p s i (a,b)) V=(Claw R p a).eval (pull s 0 V) i * (Claw R p b).eval (pull s 0 V) i:=by
    unfold duetU verseX; rw [Fin.prod_univ_two]; exact congr_arg₂ _ (slotBeamEq ..) (slotBeamEq ..)
variable {R: PathData G}{P:Clip}
lemma duet_cost (h:R.Bounds P s b U)(x:Signed)(p:PlaqAxes)(i:G.ColorIndex) : saturate (duetU R p x i) (penny R p) (s/2) (b*b) := by
    let f(j:ℕ):= ‖FareU R p j‖ * Real.exp (s* (Claw R p j).length); let g(i:ℕ×ℕ):= f i.1*f i.2; have he:SumBudget f b:= h.rows p
    have hs:0 ≤ s:=h.width.le; have hp: Summable g:= he.2.1.mul_of_nonneg he.2.1 he.1 he.1; unfold saturate; apply budget_minor (g:=g) ⟨fun i=>mul_nonneg (he.1 _) (he.1 _),hp,?_⟩ (fun _=>by positivity) ?_
    · rw [hp.tsum_prod]; unfold g; simp only [tsum_mul_left,tsum_mul_right]; apply mul_le_mul he.2.2 he.2.2 (tsum_nonneg he.1) ((tsum_nonneg he.1).trans he.2.2)
    intro j; have hu:lawn (duetU R p x i j) ≤ 2*((Claw R p j.1).length + (Claw R p j.2).length):=by unfold lawn duetU; rw [Fin.sum_univ_two]; change (slotBeam ..).leg.length + (slotBeam ..).leg.length ≤ _; rw [rangeS,rangeS]; unfold RG.Slot.length; omega
    unfold g f penny; rw [norm_mul,mul_mul_mul_comm,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity); have hp:= Nat.cast_le (α:=ℝ) |>.mpr hu; rw [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add] at hp; linarith only [mul_le_mul_of_nonneg_left hp hs]
lemma duet_funds (R:PathData G)(x:Signed)(p:PlaqAxes)(i:G.ColorIndex)(u:ℕ×ℕ): moderateX (duetU R p x i u) (heraldD G):=by intro j y;fin_cases j<;> exact brightD .. -- fills forall
abbrev voyageAt (R:PathData G)(p:PlaqAxes)(V:CoverConfig G):= ∑' i,FareU R p i • ((Claw R p i).eval V)
lemma duet_sings (h:R.Bounds P s b U)(x:Signed)(p:PlaqAxes)(V:CoverConfig G)(i:G.ColorIndex): rhythm (duetU R p x i) (penny R p) V= (voyageAt R p (pull x 0 V) i)^2 :=by
    let u:=pull x 0 V; let f(j:ℕ):= FareU R p j • ((Claw R p j).eval u); have hp : Summable f := (h.rows p).2.1.mul_right 2|>.of_norm_bounded fun j=> by
       unfold f; rw [norm_smul]; exact mul_le_mul (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg _)))) (RG.Slot.eval_norm _ u) (norm_nonneg _) (mul_nonneg (by exact abs_nonneg _) (Real.exp_pos _).le)
    have ht := rhythm_sum _ _ (duet_cost h x p i) (div_nonneg h.width.le zero_le_two) (lumenD G) (duet_funds R x p i) V
    unfold rhythm; rw [ht.tsum_prod]; change (∑' (a:ℕ) (b:ℕ), FareU R p a * FareU R p b * verseX _ _)=_; simp_rw [duoValue]; let g(j:ℕ):ℝ:= f j i; have hh(a:ℕ) (b:ℕ):FareU R p a * FareU R p b*((Claw R p a).eval u i*(Claw R p b).eval u i)=g a *g b:=by unfold g f; simp only [PiLp.smul_apply,smul_eq_mul]; ring
    change (∑' (a:ℕ)(b:ℕ),_*_*((Claw R p a).eval u i*(Claw R p b).eval u i))=((chin i) (∑' i, f i))^2; simp_rw [hh,tsum_mul_left,tsum_mul_right,(chin i).map_tsum hp,pow_two]; rfl
lemma duet_power (h:R.Bounds P s b U)(x:Signed)(p:PlaqAxes)(V:CoverConfig G):∑ i:G.ColorIndex,rhythm (duetU R p x i) (penny R p) V= ‖voyageAt R p (pull x 0 V)‖^2:=by
    simp_rw [duet_sings h x p]; rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]; simp [pow_two]
end Script
end YM.OPE.Flume
