import YM.RG3.Primary.Emboss
/-!
# Exact represented-error purchase + density on singleton after reclosure

Consumers on same d/H, root and scaling conventions. Keep d'. `Form` grants
requiring all stated γ,W support receipts before this operation on P. If
captions (fixed active global costs) entered, include their Fire eval in
pure unit coordinate. No explicit contraction of canonical coefficient.
Proportional residual and coordinate purchases important.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Primary
open RG Push.Local Press RG3.Forms Law Finset Function Source Lattice Wilson Marker Overlay Ac MeasureTheory
open Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {R : Census V} (s : V) (d : Deck R P)
variable {D : ℕ} {F : Labels.Frame G D} (A : Hol G) (C : SectionData F)

omit [Nonempty V] in
lemma name_income {w u c d' b a} (h : d.Active) (ht : d.Budget w u c d' b a) :
    w s * ‖legend s d‖ ≤ u+a := by
  have hw := ht.radial.pure
  have hS := d.captions.chords h.captions ht.captions hw |>.1
  rw [legend]
  apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (hw s).le).trans
  rw [mul_add]; refine add_le_add (ht.radial.localU _) ?_
  rw [Forms.Captions.chord, Poly.share hS]
  let f (i : ℕ) := if s∈ (d.captions.tag i).val then Poly.toll w (d.captions.tag i) * P.p.mass (d.captions.cover i) ‖d.captions.value i‖ else 0
  have hf : SumBudget f a := ht.captions.budget s
  let k i := (Poly.send (d.captions.tag i) (d.captions.value i)).part (R.fire s)
  have he (i) : w s * ‖k i‖ ≤ f i := by
    unfold k; rw [Poly.part_send]; split
    next h =>
      refine le_trans (mul_le_mul_of_nonneg_left (P.p.loMass (d.captions.cover i) _ (norm_nonneg (d.captions.value i))) (hw s).le) (le_of_eq ?_)
      unfold f; rw [← h,if_pos (show s∈ (R.fire s).val from mem_singleton_self _),Poly.solo_toll]
    rw [norm_zero,mul_zero]; exact hf.1 _
  change w s * ‖tsum k‖ ≤ a
  have hs : SumBudget (fun i => w s * ‖k i‖) a := budget_mono hf (fun i => mul_nonneg (hw _).le (norm_nonneg _)) he
  have hu : Summable (fun i => ‖k i‖) := by
    have hEq : (fun j => (w s)⁻¹ * (w s * ‖k j‖)) = (fun i => ‖k i‖) := funext fun j => by rw [←mul_assoc,inv_mul_cancel₀ (hw _).ne',one_mul]
    exact hEq ▸ (hs.2.1.mul_left (w s)⁻¹)
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hu) (hw s).le).trans ((hu.tsum_mul_left _).symm.trans_le hs.2.2)

/-- Estimate for a concrete sector representative.
To comparison: run for each aligned/extracted sector s at actual P (with
accessibility & strengthened p geometry), then apply on its own error density
or transfer. Regular and marker outputs through arbitrary p orders as stated;
K sup not derivative, filial coefficients and captured `Checked` not pushed
here. The paid assertion on the *old* root support is not the requested
later contraction estimate: must derive e.g. from an authorized bulk+section
presentation or changed sector tail and force grants. -/
theorem usable (w : ℝ) (θ : V→ℝ) (m : ℕ→ℝ) (δ : ℝ)
    (he : Readable A C P.p n w) {u c d' b a} (h : d.Budget θ u c d' b a) (hp : d.Active)
    (hs : StemPay s d A C w θ m δ) {vac mark : ℝ} (X : Billboard d.contents θ P.p.B (P.p.supportExponent+1) vac mark)
    {η k : ℝ} (hV : P.activities.Valid P.p η k) (hA : Accessible P)
    (χ γ : ℝ) (hδ : δ≤1) (hχ : 1≤χ) (hf : χ*(vac+mark)+2*δ ≤ γ) (hγ : 0≤γ)
    (green : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) (d₀ : ℝ) (hD : (Real.exp γ-1)/χ ≤ d₀*b) :
    let co := Primary.comp s d A F
    let Z := C.footprint (d.contents.origins s)
    let M := δ/(θ s)
    let B := c+δ+θ s * P.p.mass Z (w*M)
    ∃ (o : Deck R P) (T : Canonical s o A C),
      o.density=d.density ∧ o.Active ∧ o.Budget θ (u+δ) B d₀ b a ∧ o.captions=d.captions ∧ o.contents.origins=d.contents.origins ∧
      T.drawer=0 ∧ T.user=F.core co ∧ o.contents.support=copying s d C ∧ o.contents.H=sales s d A C ∧
      T.index.Format (o.contents.origins s) A P ∧ T.index.x=legend s d • F.e0+co ∧
      (θ s * ‖T.index.x 0‖ ≤ u+a+δ) ∧ (θ s * F.coeffSize (F.core T.index.x) ≤ δ) ∧
      T.index.remBound (o.contents.origins s) P b (B/(θ s)+d₀/(θ s)) ∧
      T.index.density (o.contents.origins s) C P = fun U => (d.density U).part (R.fire s) := by
  intro co Z M B
  have hθ := h.radial.pure
  have hv := hs.purchase hθ he hp
  let f := feeds s d A C he.sound.anchored
  have hx i : Feed.hot (f.mode i) := R.fire_hot _
  let Y : Forms.Test d f δ θ vac mark := {
    toBillboard := X, radii := hθ, articles := hp.articles, check := hV.forced,
    slip := kept s d A C he hp, cents := ink (F:=F) s d A w m, budget := hv,
    sufficesStamp := hδ }
  let T := dress s d A C
  let o := Y.task hA T
  obtain ⟨HL,HP',H⟩ := Y.stay χ γ hχ hf hγ green hA (funded s d A C he hp h hs)
    (fun i U => by
      unfold Feed.slip; split
      next h => exact (Poly.part_send _ _ _).trans (if_neg (Ne.symm h))
      next h =>
        have hi (j : f.office i) : Feed.hot (Feed.domain i) := by rw [← f.serves i j]; exact hx _
        unfold Feed.row; rw [tsum_congr (g:=fun _ => 0) (fun j => (h (hi j)).elim),tsum_zero,Complex.zero_re,Real.exp_zero,Complex.ofReal_one,sub_self,map_zero]; rfl) h hp hD h.radial.factor (colored s d A C he hp) (hs.log_bounds hθ he hp h) hp.captions h.captions
  -- `stay` hs0 requires pure corrections (all f PRESUPPLY terms only hot but unmentioned Column may be quiet).
  let g := drawer s d A C he hp o.contents rfl rfl rfl rfl d.captions
  refine ⟨o,g,H,HL,HP',rfl,rfl,rfl,rfl,rfl,rfl,g.healthy HL,?_,?_,?_,g.remit HP', Eq.trans
    (candle s o _ _ (g.expose HL HP') HL HP' hV) (funext fun U => congrArg (fun x : Marker.Poly R => x.part (R.fire s)) (congrFun H U))⟩
  · change ((d.contents.units s+(if s=s then co 0 else 0))+d.captions.chord.part _) • F.e0+F.core co=legend s d • F.e0+co
    nth_rw 3 [core_split F co]; unfold legend
    rw [if_pos rfl]; simp only [add_smul]; abel
  · change θ s * ‖((legend s o • F.e0 + F.core co):F.Coeff) 0‖ ≤ _
    have Hx : F.core co (0:F.Index)=0 := update_self (0:F.Index) 0 co
    rw [Pi.add_apply, Pi.smul_apply, Hx,add_zero,Labels.Frame.e0,Pi.single_eq_same,smul_eq_mul,mul_one]
    have hu := name_income s o HL HP'
    linarith
  · change θ s * F.coeffSize (F.core (legend s o • F.e0+F.core co)) ≤ _
    have H0 : F.core (F.core co)=F.core co := g.pure
    have HE : F.core F.e0 = 0 := by ext i; by_cases h : i=0 <;> simp [Labels.Frame.core,h,Labels.Frame.e0]
    rw [map_add,map_smul, HE,smul_zero,zero_add,H0]
    exact (mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans (hs.combine hθ he hp).2) (hθ s).le).trans (by rw [div_eq_inv_mul,←mul_assoc,mul_inv_cancel₀ (hθ s).ne',one_mul])
end YM.RG3.Primary
