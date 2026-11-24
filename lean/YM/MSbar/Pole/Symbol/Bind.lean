import YM.MSbar.Pole.Symbol.Exchange

/-! One line types including the polarizations needed by gluon propagators;
`query` is a cross-propagator with the Landau/N-L auxiliary field retained (Feynman gauge). -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
lemma narrow {p:ℂ→Prop} (h : ∀ᶠ z in approaching,p z) : ∃ R:ℝ, 0<R∧ ∀ z∈slit R,p z := by
  obtain ⟨b,hb,hv⟩:=mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  obtain ⟨R,hr,H⟩:=Metric.mem_nhds_iff.mp hb
  exact ⟨R,hr, fun z hz=> hv ⟨H hz.1,hz.2⟩⟩

namespace Symbol
variable {I : Type} [Fintype I] {n : ℕ}
inductive Chain (I : Type)
| scalar
| query (i:I)
| pair (a b:I)
namespace Chain
variable {Z : Chain I}
def usable : Chain I → Prop | pair a b=>a≠b | _=>True
def reads : Chain I → Finset I
| scalar => ∅ | query i=>{i} | pair a b => {a,b}
def demand : Chain I→ ℕ | scalar | pair .. => 0 | query _ => 1

/-- The first momentum `p` is the one flowing into the vertex at the first incidence. -/
def term (p : I) (w : ℂ) (F : Cloud I): Chain I → Cloud I
| scalar => F
| query i=> fun n x=> F n (update x i (x p))
| pair a b=> stroke a b w F

private def changeAt (a p : I)(n:ℕ): External I n →L[ℝ] External I n:= ContinuousLinearMap.pi fun i=> if i=a then ContinuousLinearMap.proj p else ContinuousLinearMap.proj i
private lemma changed (a p:I) (x:External I n): changeAt a p n x=update x a (x p) := by funext i; by_cases he:i=a; subst i; simp [changeAt]; simp [changeAt,he]
lemma regular {R:ℝ} {F:ℂ→Cloud I} (h : Meridian (zone R) F) (hp : Z.usable) (p : I) (hh : ∀ z∈zone R,∀ i∈Z.reads,Tone (F z) i) : Meridian (zone R) (fun z=> term p (dimension z) (F z) Z) := by
  cases Z with
  | scalar=>exact h
  | query i=>
    constructor
    · intro n; have ht := (h.budget n).affine (changeAt i p n) 0
      simp_rw [zero_add,changed] at ht; exact ht
    intro z hz; constructor
    · intro n J x; change F z n (update _ _ _)= F z n (update x i (x p))
      rw [← (h.tensor z hz).moves n J (update x i (x p))]; congr 1; ext1 a; by_cases ha:a=i; subst a; simp; simp [ha]
    intro n x; change F z (n+1) (update _ _ _)= F z n (update _ _ _); rw [← (h.tensor z hz).agrees n (update x i (x p))]; congr 1; ext1 a; by_cases ha:a=i; subst a; simp; simp [ha]
  | pair i j=> exact tracing hp h (fun z hz=>hh z hz i (by simp [reads])) (fun z hz=>hh z hz j (by simp [reads]))
lemma linear (p : I)(w c:ℂ) (F H:Cloud I) (Z:Chain I):
    term p w (c•F+H) Z = c•term p w F Z+term p w H Z:= by
  cases Z with
  | scalar | query=> rfl
  | pair i j=>
    funext n y; unfold term stroke horizontal vertical; simp only [Pi.smul_apply,smul_eq_mul, Pi.add_apply,Finset.sum_add_distrib,← Finset.mul_sum]; ring
lemma zero (p : I)(w:ℂ) (Z:Chain I): term p w 0 Z = 0:= by
  cases Z with
  | scalar | query => rfl
  | pair a b => funext n x; simp [term,stroke,horizontal,vertical]
lemma alone (p : I)(w c:ℂ)(F:Cloud I)(Z:Chain I): term p w (c•F) Z=c•term p w F Z:= by simpa [zero] using linear p w c F 0 Z

-- Extend a.e. shape hypotheses to germs at ζ=0 once known regular. Uses only
-- the same field order, comparison on all n. Useful also when applying MS counterterms.
theorem whirl {F : ℂ→ Cloud I} {k : ℕ} (h:Vortex k F) (hp : Z.usable) {U V:Finset I} (p:I) (hx:Z.reads ⊆ V) (hh : Acts U V F) : Vortex k (fun z=>term p (dimension z) (F z) Z) := by
  obtain ⟨R,G,hr,H,h⟩:=h
  obtain ⟨S,hs,hj⟩:=narrow hh
  have hr' := lt_min hr hs
  let r:=min R S; let P : ℂ→Cloud I:= fun z=>term p (dimension z) (G z) Z
  have he {z} (hz:z∈slit r): G z=z^k • F z:= by funext n x; exact (h z ⟨zone_le (min_le_left R S) hz.1,hz.2⟩ n x).symm
  have ht {z} (hz:z∈slit r): Shape U V (G z):= by rw [he hz]; exact (hj z ⟨zone_le (min_le_right ..) hz.1,hz.2⟩).scale _
  have hw : Meridian (zone r) G:=H.mono (zone_le (min_le_left ..))
  refine ⟨r,P,hr',regular hw hp p (fun z hz=>?_), fun z hz n y=> ?_⟩
  · have hu : Shape U V (G z):= by
      by_cases hi:z=0
      · subst z; refine Shape.transmitted ((neighborhood hr').mono (fun i hi=> ht hi)) (fun n x=>?_)
        exact ((hw.budget n).region _ hz _).continuousAt.continuousWithinAt
      exact ht ⟨hz,hi⟩
    exact fun i hi=> hu.angle i (hx hi)
  unfold P; rw [he hz, alone]; rfl
end Chain
end Symbol
end YM.MSbar.Pole
