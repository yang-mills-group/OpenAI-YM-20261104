import YM.Integration.QLocalFullRootedOffer
import YM.Integration.QLocalRequestedSectorSale
import YM.Integration.ManuscriptQLocalMarkedRoster
import YM.Integration.QLocalSignedMarkShipping

/-! Preselect the physical Gaussian cost of each finite signed source roster.
The purchased radius is common to all finite source truncations and fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedSourceCalendar
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Tree Precision Marker
open Push Push.SectorMeasure PhysicalNext PhysicalNext.Repeat Daisy Charity.RG12
open ConnectedActivityE6 ConnectedActivityE6.SliceRows Blaze Blaze.March Merge MergeProof RGLocalTaylor Retain Laminate
open PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite PhysicalNext.JointLoad.Psalm
open LocalComparison QLocalFullRootedOffer
open scoped Classical BigOperators

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {R : Rep G f} {W μ t C : ℝ} {Q : ConnectedActivityE6.Target G P} {O : Target.Order G W}
    {D : Stage} {Γ₀ : Target.Expense Q} {j : ℕ}

theorem joint {V : Type} (J : FullQLocal.RenderedStep.Request V) {Δ : Decal G} {quote : Libretto G J.outputFieldOrder}
    {book : QLocalRequestedSectorSale.Booking G} {patch : RG.Patch} {γ : ℝ}
    (w : QLocalRequestedSectorSale.Window J (Δ.paired (schedule G)) Q quote book patch t γ) :
    QLocalRequestedSectorSale.Window J (schedule G) Q quote book patch t γ :=
  ⟨w.heir,w.ledger,w.captain,w.outer,w.hard,w.analytic.2,w.glyph⟩

variable {V X : Type} [Fintype V] [DecidableEq V] {Γ : Census V}
    {o : V → Site f} {w : V → ℝ} {A : RG3.Script.Picnic.Taste X o R Γ} {κ a b : ℝ}
    (B : FullBudget R.p A w κ a b)

def charge (V : Type) [Fintype V] (κ a b : ℝ) : ℝ :=
  2*((Fintype.card V:ℝ)*a+(Fintype.card V:ℝ)*(κ*b))

def scale (G : Gauge) (L : Side) (t u : ℝ) := radius (Mallow.station (betaF G t L)) u

def Priced (Y : Cash W t μ L Q O C T (QLocalInheritedRegularSlots.carrier R))
    (base x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) : Prop :=
    let rows := (ManuscriptQLocalMarkedRoster.promised B base x E K).terms
    let δ := scale G L t (charge V κ a b)
    let v := fun i => δ*w i
    0<δ ∧ δ≤1 ∧
      Month (fun i=>(rows i).M) (fun i=>Menu.sumFee (rows i) v) (S.ratio.parent ∘ o)
        (fun i=>Menu.sing (rows i) v) v Y ∧
      Palette.Plot (fun i=>(rows i).M) Y (fun i=>Gala.mantle_rim G L t*Menu.sumFee (rows i) v) ∧
      ∀ i, ((Menu.sumFee (rows i) v : ℝ):ℂ) • Menu.sing (rows i) v=Menu.stamp (rows i)

/-- The original regular and forced field phases survive in each purchased
word. Its fee is measured at the stated physical radius. -/
theorem source (Y : Cash W t μ L Q O C T (QLocalInheritedRegularSlots.carrier R))
    (stamp : Stamp T) (paid : (schedule G).rub P Q Γ₀ L W μ O D j t) (exp : 4≤Q.relative)
    (card : Fintype.card V≤j+1) (base x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) :
    Priced B Y base x E K := by
  unfold Priced
  intro rows δ v
  let h := shipping Y stamp paid
  have old : Menu.Offer o rows w R.p.B R.p.supportExponent (charge V κ a b) :=
    ManuscriptQLocalMarkedRoster.offer B base x E K
  obtain ⟨positive,one,small⟩ := limited o w B.radii rows (Mallow.station (betaF G t L))
    h.positive R.p.supportExponent R.p.B old
  have hv i : 0<v i := mul_pos positive (B.radii i)
  have occ : Extra.Multi.Occupancy (S.ratio.parent ∘ o) (j+1) :=
    fun _ => (Finset.card_le_univ _).trans card
  refine ⟨positive,one,month Y o v hv rows h.positive.le h.foam h.cover exp small occ h.plain,
    plotted Y o v hv rows (zero_le_one.trans h.rim) h.positive.le h.foam h.cover exp small occ h.raised,?_⟩
  exact fun i=>Menu.purchase (rows i) hv

theorem selected (J : FullQLocal.RenderedStep.Request V) {quote : Libretto G J.outputFieldOrder}
    {book : QLocalRequestedSectorSale.Booking G} {patch : RG.Patch} {γ : ℝ}
    (window : QLocalRequestedSectorSale.Window J (schedule G) Q quote book patch t γ)
    (Y : Cash book.W t book.μ patch.L (QLocalRequestedSectorSale.target J Q) book.order C T
      (QLocalInheritedRegularSlots.carrier R)) (stamp : Stamp T) (card : Fintype.card V≤patch.J+1)
    (base x : X) (E : Finset ℕ) (K : Finset (ℕ×ℕ)) : Priced B Y base x E K :=
  source B Y stamp window.analytic (requested J Q) card base x E K

/-- One actual cash on the complete slotted input works for all finite
truncations and every test. The native ledger chooses it before them. -/
theorem purchased (J : FullQLocal.RenderedStep.Request V) {quote : Libretto G J.outputFieldOrder}
    {book : QLocalRequestedSectorSale.Booking G} {patch : RG.Patch} {γ : ℝ}
    (window : QLocalRequestedSectorSale.Window J (schedule G) Q quote book patch t γ)
    (works : Works (QLocalRequestedHeirQuote.teller J P) patch.L t S T)
    (stamp : Stamp T) (entry : Intake (QLocalRequestedHeirQuote.teller J P) T t R)
    (card : Fintype.card V≤patch.J+1) :
    ∃ Y : Cash book.W t book.μ patch.L (QLocalRequestedSectorSale.target J Q) book.order book.c T
      (QLocalInheritedRegularSlots.carrier R),
      Cash.Renewed J.outputFieldOrder (QLocalRequestedHeirQuote.toll J) 1 1 Y ∧
      ∀ base x E K, Priced B Y base x E K := by
  obtain ⟨Y,renew⟩ := (window.ledger.2 _ _ S T works).2 stamp _ (QLocalInheritedRegularSlots.intake R entry)
  exact ⟨Y,renew,selected B J window Y stamp card⟩

theorem restore_factor (G : Gauge) (L : Side) (t u : ℝ) (h : 1≤betaF G t L) :
    (1+|u|)*betaF G t L*scale G L t u=1 := by
  let β := betaF G t L
  have hp : 0<β := zero_lt_one.trans_le h
  have d : 0<1+|u| := by positivity
  have top : β⁻¹/(1+|u|)≤1 := (div_le_iff₀ d).2
    ((inv_le_one_of_one_le₀ h).trans (by linarith [abs_nonneg u]))
  unfold scale radius Mallow.station
  rw [Real.rpow_neg_one,min_eq_right top]
  change (1+|u|)*β*(β⁻¹/(1+|u|))=1
  field_simp [hp.ne',d.ne']

omit [Fintype V] in
theorem restore_word (G : Gauge) (L : Side) (t u : ℝ) (h : 1≤betaF G t L) (v : Γ.Mode) :
    Poly.toll w v=((1+|u|)*betaF G t L)^v.val.card*
      Poly.toll (fun i=>scale G L t u*w i) v := by
  rw [word w,←mul_assoc,←mul_pow,restore_factor G L t u h,one_pow,one_mul]

omit [Fintype V] in
theorem restore_power (G : Gauge) (L : Side) (t u order cost : ℝ) (h : 1≤betaF G t L)
    (v : Γ.Mode) (receipt : Poly.toll (fun i=>scale G L t u*w i) v*cost≤betaF G t L^(-order)) :
    Poly.toll w v*cost≤(1+|u|)^v.val.card*betaF G t L^((v.val.card:ℝ)-order) := by
  have hp : 0<betaF G t L := zero_lt_one.trans_le h
  rw [restore_word G L t u h v,mul_assoc]
  calc
    _ ≤ ((1+|u|)*betaF G t L)^v.val.card*betaF G t L^(-order) :=
      mul_le_mul_of_nonneg_left receipt (pow_nonneg (mul_nonneg (by positivity) hp.le) _)
    _ = _ := by rw [mul_pow,mul_assoc,←Real.rpow_natCast (betaF G t L) v.val.card,←Real.rpow_add hp,sub_eq_add_neg]

end YM.Integration.QLocalMarkedSourceCalendar
end
