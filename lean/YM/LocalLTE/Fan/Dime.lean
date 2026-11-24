import YM.LocalLTE.Fan.Buds
/-! Payment per coarse fixed anchor. The reaper uses individual bounds before summation. -/
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
variable (X:Coat T F)
-- analytic extrap weights. α & profit for ζ in [β^{−...},β].
def levy (r:ℕ→ℕ) : Veil c f→ℝ:= Sum.elim (fun i=>chip (r i)+slack) (fun _=>mini)
def jumpP (r:ℕ→ℕ) (i:Veil c f):= levy r i + Sum.elim (fun i=> (1/2:ℝ)*pie (r i)+slack) (fun _=>3) i
def claw:= (1/32:ℝ)
def fisc (R:Rep G f)(β:ℝ)(u:ℕ→ℝ) : Veil c f→ℝ:= let H {d : ℕ}(i:ℕ→Atom G d)(p:Trans f):=(i p.2.2).magnitude * β^(-claw)
    Sum.elim u (Sum.elim (H R.path.cubic) (Sum.elim (H R.path.quartic) (Sum.elim (H R.path.loop) fun _=>1)))
lemma fisc_pos {I : Rep G f} {p:ℕ→ℝ} (hp:∀ i,0≤p i) (h:0≤w)(i:Veil c f):0≤ fisc I w p i:= by
    rcases i with i|i|i|i|i; exact hp i
    all_goals first| exact zero_le_one| exact mul_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (Real.rpow_nonneg h _)
-- Harvest lower log bound on manifest. Require no spark, posture of focal i only Body. Roster sunny used to drop Shelter; equivalent gaugeability not assumed off. 
lemma bandage (h : Cash W s a L Q o t T R)(he:X.x=s)(hp:X.width=o.K)(p:Disk G c)(hh:(timeΛ X p).manifest)(b:Air f G)(i:Miniature c f) :
     |vows X R Q o.a p b (.inr (.inr (.inr (.inr i))))|≤ Q.goal L s:=by
  let Z:=timeΛ X p; let A:= worldZ Z R.beta b; have hZ: Z.x=s:=he
  let j:LogIndex c f:=.inr (.inl i)
  obtain ⟨k,y,E,hv,hF,hP⟩:= h.laws.vapors
  have he': Z.farLog R o.a Q.table b j=vows X R Q o.a p b (.inr (.inr (.inr (.inr i)))):= by
    have hX : Z.liftA R.beta b= A:= Vine.shine Z (show Room _ S _ Z.x from hZ.symm ▸ h.laws.data.room) hh _ _; unfold farLog; rw [hX]; change Z.Short _ _ _ _ _ = Polar.whelp ..; refine Polar.miniature Z o.a R Q.table (hZ.symm ▸ h.laws.data.room) hh Q.buys _ _ ?_
    unfold Healthy; rw [show RG.flags (Pressure.temp Z.x) Z.V=∅ from hh.symm]; simp
  rw [← he']; let i':Alphabet c f:= .inr (.inl j); have hu:0≤Q.relative:= by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  exact (((hP F Z hZ (show Z.width=_ from hp) hh).2.1 j b).1.trans (hF.atom hu Q.usable.le i' (show (roadway T R (radiusB s) Q.halo j).Nonempty from exChart ..)))
lemma stakes {β:ℝ} (h : Cash W s a L Q o t T R)(he:X.x=s)(hp:X.width=o.K)(p:Disk G c)(r:ℕ→ℕ)(φ:ℕ→ℝ)(b:Air f G)(hβ:1≤β)(hI:β= betaF G s L)(i : Veil c f)
   (hR:∀ (k:ℕ), i=Sum.inl k → let e:= φ k*β^(chip (r k)+slack); (∀ U,|R.activities.regularOccurrence R.p k U| ≤ e))
    (hh:(timeΛ X p).manifest)(hQ : Q.rate< mini)
    (h₂:R.p.threshold^2 ≤ β^(-claw)*β^mini)(h₃:R.beta* R.p.threshold^3 ≤ β^(-claw)*β^mini):
   |vows X R Q o.a p b i| ≤ fisc R β φ i * β^(levy r i):=by
  let Z:=timeΛ X p; let A:=worldZ Z R.beta b; have hs O : |Z.enforce (2*o.a) A O| ≤ 1:= by rw [abs_of_nonneg (Z.conserve O _ A).1]; exact (Z.conserve ..|>.2)
  have ht (j:LogLetter c f) : |Polar.frost Z o.a R A (Z.input A) j|≤ |Polar.nest T Z.x Z.V (Z.input A) R j|:=by unfold Polar.frost; rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hs _)
  let B:= -Raw.orientation*R.beta; have hz:0≤R.p.threshold:=R.p.threshold_pos.le
  have h' : |-Raw.orientation|≤1:= by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  have hB:|B| ≤ R.beta:= by unfold B; rw [abs_mul,abs_of_pos h.laws.intake.positive]; exact mul_le_of_le_one_left h.laws.intake.positive.le h'
  have H' {m:ℕ}(B':ℕ→ Atom G m)(r:ℝ) (x:Trans f) (hh:|r| *R.p.threshold^m ≤ β^(-claw)* β^mini) : |translateValue R.p B' r (Z.input A) x| ≤ ((B' x.2.2).magnitude*β^(-claw))*β^mini:=by
    have hf:0≤(B' x.2.2).magnitude:= sum_nonneg fun _ _=> abs_nonneg _
    unfold translateValue; rw [abs_mul]; have hx:= healthy_atom (B' x.2.2) R.p (pull x.1 0 (Z.input A)) x.2.1
    apply le_trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _)); refine le_trans ?_ ((mul_le_mul_of_nonneg_left hh hf).trans_eq (by ring)); exact le_of_eq (by ring)
  rcases i with i|i|i|i|i
  · apply le_trans (ht (.inl i)); change |-(R.activities.regularOccurrence _ i _)| ≤ _; rw [abs_neg]; exact hR i rfl _
  · exact (ht (.inr (.inl i))).trans (H' R.path.cubic B i ((mul_le_mul_of_nonneg_right hB (pow_nonneg hz _)).trans h₃))
  · exact (ht (.inr (.inr (.inl i)))).trans (H' R.path.quartic B i ((mul_le_mul hB (pow_le_pow_of_le_one hz R.p.threshold_le (by omega)) (pow_nonneg hz _) h.laws.intake.positive.le).trans h₃))
  · exact (ht (.inr (.inr (.inr (.inl i))))).trans (H' R.path.loop (-orientation) i ((mul_le_of_le_one_left (pow_nonneg hz _) h').trans h₂))
  refine (bandage X h he hp p hh b i).trans ?_; change Q.goal L s≤ 1*_ ; rw [one_mul]; unfold Target.goal; rw [← hI]; exact Real.rpow_le_rpow_of_exponent_le hβ hQ.le
end YM.LocalLTE.Fan
