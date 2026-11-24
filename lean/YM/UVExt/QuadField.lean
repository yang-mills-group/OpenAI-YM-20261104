import YM.UVExt.MarginalTilt
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Physical marginal only (one Coat component before logarithm); equality on real rays. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.UVExt.EnergyRay
open RG Wilson Lattice Tree Pressure ConnectedActivityE6 Coat Raw Mask Pulse Itinerary Poll Pond Gaussian MeasureTheory Measure
open scoped Topology BigOperators Classical ENNReal

variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
variable (X:Coat T F) (R:Rep G f) (t:ℝ) (Ñ:Precision.ChartRatio G) (l : Finset ℕ) (d:ℕ) (W:ℝ) (p:Molecule S)
variable {μ cst:ℝ} {L:Side} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {o:Target.Order G W}

open Matter Push.AbsoluteSums
abbrev slice := podium S G (ground R T d (X.B) p) X.B
abbrev Eye := Poll.Body (↥(slice X R d p))
abbrev Iris := F.Slice G × (Eye X R d p)

def shade (w:Iris X R d p) (i:Head S) := capsule (X.wrapY w.1) R t (spill (slice X R d p) w.2) Ñ (W:=W) (l:=l) (q:=d) i
def printed (w:Iris X R d p) := Primitive.thermal 1 (-Gaussian.value (Pond.circuit (slice X R d p) X.relating) w.2) ((slice X R d p).card) -- exp(-r quad/2); multiply by exp(+quad/2)
def mist (w:Iris X R d p) : Primitive :=
 let v := Gaussian.value (Pond.circuit (slice X R d p) X.relating) w.2
 Primitive.thermal (Real.exp v:ℝ) (-v) ((slice X R d p).card)
def markTax (i : Head S) := match i with
 | .inl A => seedPower X A
 | _ => 1

def tiltedTerm (w:Iris X R d p) (y:ℂ) := (mist X R d p w).run y * ∏ i∈p,(shade X R t Ñ l d W p w i).run y

abbrev minor := (Pond.circuit (slice X R d p) X.relating)
abbrev quarry : Measure (Iris X R d p) := (F.order G).prod <| (Pond.arch (slice X R d p) X.relating)
def subtotal (y:ℂ) := ∫ w, tiltedTerm X R t Ñ l d W p w y ∂quarry X R d p

def project (z : F.Slice G × Air f G) := (z.1, Pond.swim (slice X R d p) z.2)
def respray (w:Iris X R d p) := (w.1,Pond.spill (slice X R d p) w.2)
def enlarge (r:ℝ) (w : Iris X R d p) := (w.1, Real.sqrt r • w.2)
lemma project_round (w:Iris X R d p) : project X R d p (respray X R d p w) = w := Prod.ext rfl (Pond.settled ..)
lemma enlarge_spill (r:ℝ) (w : Iris X R d p) : respray X R d p (enlarge X R d p r w)=(w.1, Real.sqrt r • (spill (slice X R d p) w.2)) := by
  refine Prod.ext rfl ?_; change Pond.spill _ (Real.sqrt r • _) = _ • _; ext i; simp only [Pond.spill, PiLp.smul_apply]; split <;> simp [*]

def sterile (r:ℝ) (w) := X.body (scaled R r) Ñ W t l d p (respray X R d p w)

def fees := (slice X R d p).card + ∑ i∈p, markTax X i
lemma covers (w:Iris X R d p) (z:ℂ) (hz:0<z.re) : ‖tiltedTerm X R t Ñ l d W p w z‖ ≤ (‖z‖/z.re)^(fees X R d p) * ‖tiltedTerm X R t Ñ l d W p w z.re‖ := by
 have hs : ∏ i∈p, ‖(shade X R t Ñ l d W p w i).run z‖ ≤ ∏ i∈p, ((‖z‖/z.re)^markTax X i * ‖(shade X R t Ñ l d W p w i).run z.re‖) := by
    apply Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=> ((shade X R t Ñ l d W p w i).angular _ hz).trans _)
    intro i _; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply pow_le_pow_right₀
    exact (one_le_div hz).2 (Complex.re_le_norm z)
    rcases i with A|u|u|u <;> simp only [markTax, shade, capsule]
    · rfl
    · change 0 ≤ 1; omega
    · split <;> simp [Primitive.tax]
    change 0≤1; omega
 rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hs
 unfold tiltedTerm; simp_rw [norm_mul,norm_prod]; have ht := (mist X R d p w).angular _ hz
 apply (mul_le_mul ht hs (Finset.prod_nonneg (by intros; positivity)) (by positivity)).trans; unfold fees; rw [pow_add]; dsimp only [mist,Primitive.tax] at *; apply le_of_eq; ring

lemma fog (w:Iris X R d p) (r:ℝ) (hr:0<r) : (mist X R d p w).run r = (Gaussian.tilt (minor X R d p) r w.2:ℝ) := by
 rw [mist, Primitive.standard _ _ _ _ hr]; change _= (↑(√r ^ _*Real.exp _):ℂ); push_cast
 simp only [Fintype.card_coe,Real.exp_neg]; ring_nf; rw [Complex.exp_add]; ring
 -- issue term count Finset.card vs Fintype.card

lemma on_real (w:Iris X R d p) (z:ℝ) (hz:0<z) (hp:0<R.beta) (hÑ:Ñ.scale≠0) : tiltedTerm X R t Ñ l d W p w z = (Gaussian.tilt (minor X R d p) z w.2 * sterile X R t Ñ l d W p z (enlarge X R d p z w) :ℝ) := by
 rw [tiltedTerm,fog _ _ _ _ _ _ hz,sterile,enlarge_spill]; unfold shade
 simp_rw [restores _ _ _ _ _ _ hz hp hÑ _]; rw [← Complex.ofReal_prod,← Complex.ofReal_mul]; rfl

variable (H:Cash W X.x μ L Q o cst T R) (hk:X.width=o.K)
include H hk
lemma projecting (hm : X.manifest) : MeasurePreserving (project X R d p) ((F.order G).prod X.dice) (quarry X R d p) := by
  have hp := (H.laws.data.localP F X rfl hk hm).sails.fullC.posSemidef
  exact (MeasurePreserving.id _).prod (Pond.orbit hp (slice X R d p))
lemma cut_sweeps (z : F.Slice G × Air f G) : X.body R Q.table W o.a l Q.halo p (respray X R Q.halo p (project X R Q.halo p z)) = X.body R Q.table W o.a l Q.halo p z := by
  have hS : H.unionP p= ground R T Q.halo (X.B) p := by rfl
  have he : Borough (X.wrapY z.1) (X.wrapY z.1) (H.unionP p) (spill (slice X R Q.halo p) (swim _ z.2)) z.2 l l R :=
       ⟨Village.refl .., by rw [hS]; exact (Pond.observe _).mp ((Pond.settled _ _)), fun _ _=>Iff.rfl⟩
  exact H.concord p _ _ he rfl (Finset.Subset.refl _)

lemma body_m (i : Head S) : Measurable (fun z:F.Slice G × Air f G=>(X.wrapY z.1).vertex R Q.table W o.a l Q.halo z.2 i) := by
 obtain hv:=H.laws.data.access; rw [← hk] at hv
 exact X.vertex_b Q.table_exists H.laws.intake hv o.a l Q.halo i measurable_fst measurable_snd
omit H in
lemma sterile_m {r : ℝ} (H:Cash W X.x μ L Q o cst T (scaled R r)) : Measurable (sterile X R o.a Q.table l Q.halo W p r) := by
 have he : sterile X R o.a Q.table l Q.halo W p r=fun x=> ∏ i∈p,(X.wrapY x.1).vertex (scaled R r) Q.table W o.a l Q.halo (Pond.spill (slice X R Q.halo p) x.2) i := by rfl
 rw [he]; refine p.measurable_fun_prod fun i _=> ?_
 let P : Iris X R Q.halo p → (F.Slice G × Air f G) := respray X R Q.halo p
 change Measurable ((fun z:F.Slice G × Air f G=>(X.wrapY z.1).vertex (scaled R r) Q.table W o.a l Q.halo z.2 i)∘P)
 apply (body_m X (scaled R r) l W H hk i).comp
 exact measurable_fst.prodMk ((Pond.spill_m _).comp measurable_snd)

variable {r : ℝ} (H₀:Cash W X.x μ L Q o cst T (scaled R r)) (hX:X.manifest) (hr:0<r)
include hX H₀
omit H
lemma sterile_integrable : Integrable (sterile X R o.a Q.table l Q.halo W p r) (quarry X R Q.halo p) := by
  let m:= ((F.order G).prod X.dice); let g:=sterile X R o.a Q.table l Q.halo W p r; let π:=project X R Q.halo p
  have he z : g (π z)=X.body (scaled R r) Q.table W o.a l Q.halo p z := cut_sweeps X (scaled R r) _ _ _ H₀ hk z
  have hm : Integrable (g ∘ π) m := by
     convert H₀.integrated X rfl hk hX l p using 1
     funext z; exact he z
  let hx := projecting X (scaled R r) Q.halo W p H₀ hk hX
  have : MeasurePreserving π m (quarry X R Q.halo p) := by exact hx
  rw [← this.map_eq]; exact (integrable_map_measure ((sterile_m X R l W p hk H₀).aestronglyMeasurable) this.measurable.aemeasurable).mpr hm

lemma minor_pd : (minor X R Q.halo p).PosDef := ((H₀.laws.data.localP F X rfl hk hX).sails.fullC).submatrix Subtype.val_injective
end YM.UVExt.EnergyRay
