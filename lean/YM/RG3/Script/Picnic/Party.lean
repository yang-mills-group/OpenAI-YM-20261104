import YM.RG3.Script.Picnic.Pasture

/-! # Export actual and error Passport-level certs and exact
singleton capture data. Full cost inputs per Scripts, uniform in supplied Ω
for all test data represented; can recover radii & per-slot estimates at will
later. No operation hidden inside a post-hoc quotient norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Law RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition RG3.Primary Push.Local Source Estate
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V : Type} [DecidableEq V][Fintype V][Nonempty V]{R:Census V}{ζ : V→Site n}{G : Gauge}
  {Θ : Type*}[Nonempty Θ]{P : Rep G n} {d z:Taste Θ ζ P R}
  {Et : Θ→Edition ζ R G}{A:Estate n R} {ι:Type*} [Countable ι] {T : Θ→ Estate.Truss A ι G}
  {F:Θ→ℕ→ Config G n→ℂ}{w:V→ℝ}{D: V→ℕ}{H: Hol G}{I:(s:V)→Labels.Frame G (D s)}{L:(s:V)→SectionData (I s)}{k:V→ℝ}(hr:∀ s,Readable H (L s) P.p n (k s))
variable {a u s fit sig δ vac mark c₁ t₁ c₀ t₀ κ u₀ u₁ a₀ a₁ K:ℝ} {M:ℕ} {m f₁ f₀ g : ℕ→ℝ}{t:ι→ℝ}
variable (hd: d.Snacks w u₀ c₀ t₀ κ a₀)(hz:z.Snacks w u₁ c₁ t₁ κ a₁)(hv:Voucher Et P.p w (P.p.supportExponent+1+1) u s a f₀ g)
    (hi:∀ x,(T x).Agreement (F x) w P.p ζ M (P.p.supportExponent+1) fit sig f₁)
    (hF:∀ x,(T x).Strap w P.p (P.p.supportExponent+1+1) sig t)(hx:∀ x y,(T x).filing=(T y).filing)
    (Keep: ∀ x,(d.leaf x).log=(z.leaf x).log+(Et x).log P.p+((T x).strand P.p).tally)(hf:0≤fit)(hs:0 ≤ sig)
    (hh:∀ x,Loaded H (P.p.supportExponent+1+1) m δ L (d.leaf x) (logo (ζ:=ζ) Et A F x) k w)
    (hK:∀ i,expense P.p.B (P.p.supportExponent+1+1) ((L i).footprint (ζ i)) (k i) ≤ K)
include hr hd hz hv hi hF hx Keep hf hs hh hK

set_option maxHeartbeats 500000 in
theorem reader {χ γ q : ℝ} (hc : d.Menu w vac mark)(hx' : 1 ≤ χ) (hγ : 0≤γ)(hOne : Estimate M P fit sig δ ≤ 1)
    (hall : χ*(vac+mark)+2*Estimate M P fit sig δ ≤ γ)(green:(P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1)
    (hδ:(Real.exp γ-1)/χ ≤ q *κ) (HA:Accessible P) {μ r:ℝ}(hp:P.activities.Valid P.p μ r):
    let gap:= s+fit+δ+K*δ
    let R₀ x:= logo (ζ:=ζ) Et A F x
    let R':=ripe d Et A F H L
    ∃ o : Taste Θ ζ P R,
      let E:=balance o z R'
      Nonempty (o.Snacks w (u₁+(u+δ)) (c₁+gap) q κ (a₁+a)) ∧ Nonempty (E.Snacks w (u+δ) gap (q+t₁) κ a) ∧
        (∀ x,(o.leaf x).density = (d.leaf x).density ∧
          (o.leaf x).log=(z.leaf x).log+(E.leaf x).log ∧
          (∀ i U,(o.leaf x).contents.each i U=(z.leaf x).contents.each i U+ ((E.leaf x).contents.each i U-Kbase i U P)) ∧
          ∀ i : V, ∃ Q : Coefficient (I i) n, Q.x=legend i (E.leaf x) • (I i).e0+(I i).core ((R₀ x).petition H (d.leaf x) i) ∧
            Q.Format (ζ i) H P ∧ Q.remBound (ζ i) P κ (gap/(w i)+(q+t₁)/(w i)) ∧ w i*‖Q.x 0‖ ≤ (u+δ)+a ∧ w i*(I i).coeffSize ((I i).core Q.x) ≤ δ ∧
            (Q.density (ζ i) (L i) P=fun U=> ((d.leaf x).density U).part (R.fire i)-((z.leaf x).density U).part (R.fire i))):=by
  intro gap c C
  obtain ⟨J,⟨L'⟩,HV,⟨HT⟩,hl,hs'⟩:= compilation hr hd hz hv hi hF hx Keep hf hs hh hK
  have hw:=hd.strong.radii
  have hA x:=(d.snack hd x).1
  have h c:=(d.snack hd c).2
  let out:= retire hc L' hw hp.forced J hA hOne HA
  obtain ⟨⟨Q⟩,Hq⟩:= imprint hc L' hw hp.forced J hA hOne HA χ γ hx' hall hγ green HT hδ hd.strong.divisor h
  let E:=balance out z C
  obtain ⟨W⟩:= coins (T:=C) out z HV (show P.p.supportExponent ≤ _ by linarith) Q hz
  refine ⟨out,⟨Q⟩,⟨W⟩,fun x=>?_⟩
  obtain ⟨hOut,hN⟩:= out.snack Q x; obtain ⟨hX,hY⟩:= z.snack hz x
  have hC: (E.leaf x)= Edition.jetty (out.leaf x) (z.leaf x) (C x):= even _ _ _ HV.toFirm x -- .. followed by args
  have hk i U : _= _:= packed (out.leaf x) (z.leaf x) hN hY hOut hX hp (C x) i U
  have hE i U:(out.leaf x).contents.each i U= (z.leaf x).contents.each i U+ ((E.leaf x).contents.each i U-Kbase i U P):=hC ▸ hk i U
  have Ht : (out.leaf x).log=(z.leaf x).log+(E.leaf x).log := by rw [hC]; exact (Hq x).2.trans (hl x)
  refine ⟨(Hq x).1,Ht,hE,fun i=>?_⟩
  obtain ⟨hH,hY'⟩:= E.snack W x
  let D:=c x
  have H' := (trunk hr (d.root) (d.snack hd x).1 (hs' x) (hh x) hw (by have:=P.p.exponent_pos; linarith) i).2.2.2.2
  have h' : w i*(I i).coeffSize (D.petition H (d.leaf x) i) ≤ δ:= by exact (mul_le_mul_of_nonneg_left H' (hw i).le).trans_eq (by field_simp [(hw i).ne'])
  obtain ⟨h1,h2,h3,h4,h5,h6⟩:=income (d.leaf x) (c x) hw i (hr i) (z:=E.leaf x) E.root (by rw [hC]; rfl) (hs' x) (d.snack hd x).1 d.root hY' hH hp h'
  have HEq: (E.leaf x).contents.origins=ζ:=E.root
  rw [HEq] at h4 h5 h6
  have hw i := one_stamp (out.leaf x) (z.leaf x) (E.leaf x) hOut hX hH hN hY hY' hp Ht hE i
  refine ⟨_,h1,h4,h5,h2,h3,h6.trans ?_⟩
  funext U
  rw [← (Hq x).1]
  exact (eq_sub_of_add_eq' (hw i U).symm)
end YM.RG3.Script.Picnic
