import YM.PhysMS.Frame.NestToll

/-! # Actual OPE bounds in the same normalization as the perturbative comparison

Deals with transmitting parts I--IV OPE data *on this same construction* to the
continuous measured X-frame. Nontrivial since exterior fields are at macroscopic distance,
NOT moving with either coupling-power or length scale, and interior relative scales can
vary independently without a lower cutoff. We normalize the inputs at root scale r (one
may transport again within these bounds at cost). Thus root cost loses the input normalization
power, but it remains in the inner factors. Use even for positive output. These are
subpower prices (no fixed log exponent claimed) and don't already assert perturbative
asymptotics of positive-output columns. E.g. pricing the output after pulling back through the
filter by less than any power of length doesn't justify multiplying by a fixed perturbative
coupling-order remainder in these units. The `reported` Formulas here use R.trunc,
i.e. apply projections on fixed physical fields before changing frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Filter Set Spec OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree Trace.Pilot
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(H:Leading F J)(h:Uniform F R)
    {n:ℕ}{X:Fin n→Nesting.Tree} {W I : Type} [Fintype W]
set_option quotPrecheck false
local notation "Ω" => Nesting.Tree.fork n X
local notation "Q" => F.sector.derivatives
local notation "D" d => (Climb.Bel C.book).Field d

/-- Define measured labels with the same massless/operator field convention at root length. -/
def born {I:Type}{d:I→ℕ}(r:ℝ)(v:(i:I)→(Climb.Bel C.book).Field (d i)):Labels S d :=fun j=> J r (d j) (v j)

lemma matchInvoice {Y:Type}[Fintype Y] {d b:Y→ℕ}{e:W→ℕ} (hp:d≤b) (m:ℕ)
    {x:Y→E4} {y:W→E4} (z:E4)(p:Labels S d)(w:Labels S e) (ρ:Viewers F)(hv: Injective (beside x y)) :
    Levy.invoice F R z w ρ m x y p=Levy.invoice F R z w ρ m x y (fun j=>(Q).rise (hp j) (p j)):=by
   rw [← Levy.invoice_paid,← Levy.invoice_paid]; unfold balance whole
   let a:Labels S (Sum.elim d e) :=stages p w; let a':Labels S (Sum.elim b e) := stages (fun j=>(Q).rise (hp j) (p j)) w; have h₁:Sum.elim d e≤ Sum.elim b e:= fun i=> by cases i; apply hp; exact le_rfl
   have ha(i):a' i=(Q).rise (h₁ i) (a i):=by
       cases i with
       | inl => rfl
       | inr i => exact ((Q).arrival R.continuum.laws.toSymmetric R.lifts (a (.inr i))).symm
   apply congr_arg₂ HSub.hSub
   · exact (Levy.inclusionMoment F _ _ h₁ a (beside x y) ρ hv).trans (congr_arg (Orbits.moment (spectator F ρ) _) (funext (fun i=> (ha i).symm)))
   exact Finset.sum_congr rfl fun i _=> congr_arg (upon (spectator F ρ) i.val z y w) (R.fresh_inclusions ..).symm

lemma phase_invoice {Y:Type}[Fintype Y] {d:Y→ℕ}{e:W→ℕ} (m:ℕ)
    (x:Y→E4) (y:W→E4) (z:E4)(p:Labels S d)(w:Labels S e)(ρ:Viewers F) :
    formula F R x z p y w m ρ= Levy.invoice F R z w ρ m x y p := (Orbits.tested_fields (x:=x) (w:=w) ..).symm.trans (Levy.invoice_paid ..)

open Toll
variable {d: (fork n X).Leaf→ℕ}{e:W→ℕ}{l:Filter I}{r:I→ℝ}{s:I→(fork n X).Inner→ℝ}{x:I→Tree.Plot (fork n X)}
variable {y:I→ W→E4} (M η δ ε:ℝ)(hM:0≤M)(hη:0<η)(hδ:0<δ)(he:0<ε)
variable (hr:Tendsto r l trail) (hs:∀ᶠ i in l, Accept (r i) M η (s i) (x i)) (hy:∀ᶠ i in l,Buffer (x i) (y i) δ)
variable (v:(i:(fork n X).Leaf)→(Climb.Bel C.book).Field (d i))(w:Labels S e)(m:ℕ)
include hr h hM hη hs hδ hy
private lemma lies_here : ∀ᶠ i in l, Kernel.cardPanel (x i) (y i) ∈ guardZone F R m :=by
    have ht:= hr.eventually (h.tested n X W (fun _=>⟨0,S.unit 0⟩) (fun _=>⟨0,S.unit 0⟩) m M η 1 δ hM hη one_pos hδ)
    filter_upwards [ht,hs,hy] with i hi he hv using (hi _ _ _ he hv).1
include H he
private lemma transported (p:I→Viewers F) : RateLE l (LogV ∘ r) (fun i=> ((↑((interiorBill d ε (s i))⁻¹):ℂ) • formula F R (Tree.profile (x i)) (anchor (x i)) (born J (C:=C) (d:=d) (r i) v) (y i) w m (p i))) (-(m+1:ℝ)):=by
   simp_rw [phase_invoice]; let P (i:I)(d'):=(Levy.invoice F R (d:=d') (anchor (x i)) w (p i) m (Tree.profile (x i)) (y i))
   apply rate_now F J R H P hr (hs.mono fun i h=> h.levels) (hs.mono fun i h=>h.scale) he v
   · intro e hv u ε hu
     filter_upwards [hs,hy,hr.eventually (h.tested n X W (Orbits.tags u) (Orbits.tags w) m M η ε δ hM hη hu hδ)] with i hi hh hk; unfold P; rw [← phase_invoice]; exact (hk (s i) (x i) (y i) hi hh).2.2 _
   intro e he; filter_upwards [lies_here F R h M η δ hM hη hδ hr hs hy m] with i hi u; exact matchInvoice F R he m _ _ _ _ hi.2.1

omit hr hs hy
theorem reported : ∀ᶠ r in trail, ∀ (s:(fork n X).Inner→ℝ)(x:(fork n X).Plot)(y:W→E4), Accept r M η s x→Buffer x y δ→
    let u:= r^(m+1-ε)* interiorBill d ε s
    Kernel.cardPanel x y∈guardZone F R m ∧ ‖algebraError F R (Tree.profile x) (anchor x) (born J (C:=C) (d:=d) r v) y w m‖ ≤ u ∧
    ∀ p:Viewers F, ‖formula F R (Tree.profile x) (anchor x) (born J (C:=C) (d:=d) r v) y w m p‖ ≤ u:=by
   let V:= ((Ω).Inner→ℝ) × (Ω).Plot × (W→E4) × Viewers F
   let K r (p:V):= Accept r M η p.1 p.2.1 ∧ Buffer p.2.1 p.2.2.1 δ
   let A r (p:V):= ((↑((interiorBill d ε p.1)⁻¹):ℂ) • formula F R (Tree.profile p.2.1) (anchor p.2.1) (born J (C:=C) (d:=d) r v) p.2.2.1 w m p.2.2.2)
   have hp:= uniform_power (P:=K) (m:=(m:ℝ)+1) (Y:=A) he (fun u l hN ht H₁=> transported F R J H h M η δ ε hM hη hδ he (show Tendsto id l trail from tendsto_id.mono_left ht) (s:=fun i=>(u i).1) (x:=fun i=>(u i).2.1) (H₁.mono fun i h=> h.1) (y:=fun i=>(u i).2.2.1) (H₁.mono fun i h=> h.2) v w m (fun i=>(u i).2.2.2))
   filter_upwards [hp,h.tested n X W (fun _=>⟨0,S.unit 0⟩) (fun _=>⟨0,S.unit 0⟩) m M η 1 δ hM hη one_pos hδ] with r hp ht s x y hx hy u
   have hX:= (ht s x y hx hy).1; have hS:= paid_int d ε s hx.levels
   have hV(p) : ‖formula F R (Tree.profile x) (anchor x) (born J (C:=C) (d:=d) r v) y w m p‖ ≤ u:=by
     have hv:= hp (s,x,y,p) ⟨hx,hy⟩; unfold u; unfold A at hv; dsimp only at hv
     rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hS.le),inv_mul_le_iff₀ hS,mul_comm (interiorBill ..)] at hv; exact hv
   exact ⟨hX,(glance_contract F ((norm_nonneg _).trans (hV none))|>.mpr (fun p=> (congr_arg norm (formula_seen F R _ _ _ y w m p hX.2.1 hX.2.2)).le.trans (hV p))),hV⟩

-- Output pulled at its own finite stage; a normalized estimate for its full vector.
def row (J:ℝ→tower S) (m:ℕ) {Y:Type}[Fintype Y] (x:Y→ E4)(z:E4){d:Y→ℕ}(v:(i:Y)→(Climb.Bel C.book).Field (d i))(r:ℝ):=
   (J r m).symm (R.fresh m x z (born J (C:=C) (d:=d) r v))
private def readerLine {d:(fork n X).Leaf→ℕ} (p:(fork n X).Leaf→E4) (o:E4)(m:ℕ)(a:R.channels m):=
    ((R.basis m).coord a).compMultilinearMap ((R.fresh (d:=d) m p o).codRestrict (R.stratum m) (fun v=>R.fresh_mem m p o v))
omit hδ
include hr hs
private lemma ledger : RateLE l (LogV ∘ r) (fun i=> ((↑((interiorBill d ε (s i))⁻¹):ℂ) • row F R J m (d:=d) (Tree.profile (x i)) (anchor (x i)) v (r i))) 0 := by
   let φ i:=Tree.profile (x i); let o i:=anchor (x i); let V i:= R.fresh m (φ i) (o i) (born J (C:=C) (d:=d) (r i) v); let f i:ℂ:=↑((interiorBill d ε (s i))⁻¹)
   have heq(i): f i • V i= ∑ c:R.channels m, (f i • R.coef m c (φ i) (born J (C:=C) (d:=d) (r i) v) (o i)) • R.actor m c:=by unfold V; rw[←R.assemble,Finset.smul_sum]; exact Finset.sum_congr rfl fun c _=> (mul_smul ..).symm
   have hz:RateLE l (LogV ∘ r) (fun i=> f i • V i) (-(m:ℝ)):=by
      simp_rw [heq]; apply RateLE.sum (to_log_zoom.comp hr); intro a _
      let P i d' := readerLine F R (d:=d') (φ i) (o i) m a; have hA:= rate_now F J R H (s:=s) P hr (hs.mono fun i h=> h.levels) (hs.mono fun i h=>h.scale) he v (m:=(m:ℝ)) ?_ ?_
      · exact (hA.smul (RateLE.const (R.actor m a) (to_log_zoom.comp hr))).mono (by linarith only [])
      · intro e _ u ε hε; filter_upwards [hs,hr.eventually (h.direct n X (Orbits.tags u) m a (fun _=>m) M η ε hM hη hε)] with i hp hi; exact (hi _ _ hp).2.2.1
      intro e he; exact Eventually.of_forall fun i p=> R.inclusions .. -- order?
   have hw:= (inverse_rate F m J H).comp hr
   refine RateLE.mono (RateLE.bil (u:=fun i=>f i • row F R J m (d:=d) (φ i) (o i) v (r i)) (X:=(S.Field m →L[ℂ] (Climb.Bel C.book).Field m)) hw hz ?_) (by linarith only [])
   refine Eventually.of_forall fun i=> ?_
   change ‖ f i • backward m J (r i) (V i)‖ ≤ _; rw [← map_smul]; exact ContinuousLinearMap.le_opNorm ..

omit hr hs
theorem coef : ∀ᶠ r in trail, ∀ (s:(fork n X).Inner→ℝ)(x:(fork n X).Plot), Accept r M η s x →
     ‖row F R J m (d:=d) (Tree.profile x) (anchor x) v r‖ ≤ r^(-ε) * interiorBill d ε s := by
   let V:= ((Ω).Inner → ℝ) × (Ω).Plot; let K r (p:V) := Accept r M η p.1 p.2
   let P r (p:V):= (↑((interiorBill d ε p.1)⁻¹):ℂ) • row F R J m (d:=d) (Tree.profile p.2) (anchor p.2) v r
   have hp:= uniform_power (P:=K) (m:=0) (Y:=P) he (fun u l hN ht H₁=> neg_zero (G:=ℝ)|>.symm ▸ ledger F R J H h M η ε hM hη he (show Tendsto id l trail from tendsto_id.mono_left ht) (s:=fun i=>(u i).1) (x:=fun i=>(u i).2) H₁ v m)
   filter_upwards [hp] with r hp s x hx; have hv:=hp (s,x) hx; have hs:= paid_int d ε s hx.levels; unfold P at hv
   dsimp only at hv; rwa [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),inv_mul_le_iff₀ hs,mul_comm (interiorBill ..),zero_sub] at hv
end YM.PhysMS.Frame
