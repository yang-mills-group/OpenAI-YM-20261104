import YM.LocalLTE.Quartz.Points
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
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
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
-- Maneuvers depend on V generic. Carrier.P.Slot all.S.Fin count.Bound independent periods.
variable (φ':Veil c f→ℝ) (h':∀ i,0≤φ' i) (rA:ι→ℝ) (hr:∀ i,0≤rA i)
local notation "Y'"=> betaF G t L
local notation "Ω"=> Merge.Tickets (Merge.Palette.sign M S)

variable  {W' V:ℝ} (u:Site c)(ht:let Y := neighbors (East.stagnate q Q.halo*(radiusB t)) u; SumBudget (fun i=> if traceO S R i ∈Y then φ' i else 0) V) (hp : SumBudget (Merge.Palette.wages M rA) W') -- Term Stage.B' unresolved.L.


section
variable [Fintype ι] (C₁:Captain H j C d v e B' v₁ y B η k χ)
-- ex.C inert lifted.H.Hoch ℝ→ℝ.
variable (D':ℕ→ℝ)(hD:∀ i,1 ≤ D' i)

local notation "E₀"=> Height.grow G L t
local notation "b'"=> (betaF G t L)
variable (hB:1 ≤ betaF G t L)
variable (P':ℕ)(ħ:Candor M z D q n r₀ A') (Z:ℝ)(β:ℝ)
include hr hB hD C₁
lemma ticketsT (h:Ac.Hit (Captain.reachability (H:=H)) (radiusB t) (fun z=> Height.beaconN H q z* Height.rocket H D' z * Height.markU C₁ M rA z P') Z β):
    Ac.Hit (fun i: Stars H M=>reachability i.1) (radiusB t) (Fan.wagesZ M H χ q k rA C₁ D' P') Z β:=by
    intro i; let b z:= if i∈ Captain.reachability (H:=H) z then Height.beaconN H q z* Height.rocket H D' z * Height.markU C₁ M rA z P'*Real.exp (Z*coverNumber (radiusB t) (reachability z)) else 0
    refine sigma_total (fun x:Stars H M=> if i∈ reachability x.1 then Fan.wagesZ M H χ q k rA C₁ D' P' x*Real.exp (Z*coverNumber (radiusB t) (reachability x.1)) else 0) b ?_ (h i); intro j;  have he(i'):0≤ Fan.wagesZ M H χ q k rA C₁ D' P' i':= Fan.roaring M H χ q k rA hr C₁ D' hD _ _ hB -- edit
    refine budget_finite (fun k=> ?_) ?_
    · dsimp only; split; exact mul_nonneg (he _) (Real.exp_nonneg _); exact le_rfl
    unfold b; dsimp only; by_cases hk : i∈ reachability j
    · 
       simp_rw [if_pos hk]; unfold Fan.wagesZ; dsimp only; rw [← sum_mul, ← debtU]
       refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (Real.exp_pos _).le; rw [Finset.mul_sum]; apply sum_congr rfl; intros; ring
    ·  simp_rw [if_neg hk,sum_const_zero];exact le_rfl
-- price.P.weight.ALL. Need conversion.Work. root support any
omit hr hB hD C₁
def Enter (Z:Stars H M):= ∃ i,(Z.2 i).val.Nonempty
variable (r: ℝ)(hw:0≤r)(aA:ι→ℝ)(L₁ : ι→ℝ)(ha:∀ i,1 ≤ aA i)(hP:∀ i,rA i=aA i *L₁ i)(hA:∀ i,0 ≤ L₁ i) (hm:∀ i,¬A' i→ r ≤ aA i)
omit [Fintype ι] in
lemma braceT (V: Stars H M) (u v:ι→ℝ): pearl V.fst M (fun i=>u i*v i) V.snd=pearl V.fst M u V.snd * pearl V.fst M v V.snd:=by unfold pearl; simp_rw [prod_mul_distrib]
include ha hP hA hm
omit [Fintype ι] in -- hB already omitted
lemma lance (V:Stars H M)(hh:∃ i,∃ j:ι, j∈(V.2 i).val ∧ ¬A' j) : r*pearl V.1 M L₁ V.2≤ pearl V.1 M rA V.2 :=by
   rw [funext hP, braceT]; obtain ⟨i,k,hi,h⟩:=hh; refine mul_le_mul_of_nonneg_right (le_trans (hm _ h) ?_) (pearlsNN M H L₁ hA _)
   have hX (q):1≤∏ j∈ (V.2 q).val,aA j:= Finset.one_le_prod (fun _ _=>ha _); unfold pearl
   rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ i)]; apply le_trans (b:=∏ j∈(V.2 i).val,aA j) (?_) (le_mul_of_one_le_right (zero_le_one.trans (hX _)) (Finset.one_le_prod fun v _=>hX _))
   rw [← Finset.mul_prod_erase (V.2 i).val _ hi]; exact le_mul_of_one_le_right (zero_le_one.trans (ha _)) (Finset.one_le_prod fun j _=>ha _)
omit hm
include hD ha hP hA hB C₁
omit [Fintype ι] in
lemma belayed (V: Stars H M) : let v := pearl V.1 M L₁ V.2 * wife C₁ V.1 M V.2 P'; let e := Height.beaconN H q V.1; let b:= Height.rocket H D' V.1; v ≤ wagesZ M H χ q k rA C₁ D' P' V ∧ e*v ≤ wagesZ M H χ q k rA C₁ D' P' V ∧ b*v ≤ wagesZ M H χ q k rA C₁ D' P' V:=by
    intro v e b; have he:1 ≤ e:= Fan.bloomT M H q hB V -- edit
    have hb: 1 ≤ b:= East.toll H D' hD _; have hg:0 ≤ wife C₁ V.1 M V.2 P':= mul_nonneg (pow_nonneg (by unfold March.shiftG; positivity) _) (fareV ..)
    have hh':1≤ pearl V.1 M aA V.2:= Finset.one_le_prod (fun i _=> one_le_prod (fun i _=>ha i));have hh:= pearlsNN M H L₁ hA V
    have h:0≤ v:= mul_nonneg hh hg; have ht: e*b*v≤ wagesZ M H χ q k rA C₁ D' P' V:= by unfold wagesZ; rw [funext hP, braceT]; unfold v; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hg; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hh hh') (mul_nonneg (zero_le_one.trans he) (zero_le_one.trans hb))
    exact ⟨(le_mul_of_one_le_left h (one_le_mul_of_one_le_of_one_le he hb)).trans ht,(mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans he) hb) h).trans ht,(mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans hb) he) h).trans ht⟩
include hm hw
variable (hL:∀ i, r₀ i≤ n → R.activities.E i≠0→ (R.activities.reg i).support ⊆ Animals.neighbors (S.patch.L.val*radiusB t) (R.activities.reg i).site)
    (hT:∀ i,A' i →∀ j,(M i).turn= Wing.logKey j→ (R.activities.reg j).support⊆Animals.neighbors (S.patch.L.val*radiusB t) (R.activities.reg j).site)
variable (hΥ:∀ i,R.activities.E i ≠ 0 → n< r₀ i→ r ≤ D' i)
    (hc : Height.grow G L t^q ≤Real.exp (Q.mark L μ t)) (hcc : Height.grow G L t^q ≤ Real.exp (Q.ε*Pressure.Stores.till t)) (hF:r≤ Height.grow G L t^q)
include hΥ hc hcc hL hT hF
omit [Fintype ι] in
lemma exhausted (z:Stars H M) (X:Config G c)(h:Enter M H z)(ht: wingTerm (χ:=χ) z.1 M z.2 X≠0) (hR:¬ Candor M z.1 z.2 q n r₀ A'):
    r*(pearl z.1 M L₁ z.2 * wife C₁ z.1 M z.2 P')≤ wagesZ M H χ q k rA C₁ D' P' z:=by
    let v := pearl z.1 M L₁ z.2 * wife C₁ z.1 M z.2 P'; let S:= Height.beaconN H q z.1; let V:=wagesZ M H χ q k rA C₁ D' P' z
    let c:= Height.rocket H D' z.1
    have hg:= belayed M H χ q k rA C₁ D' hD hB P' aA L₁ ha hP hA z -- order
    have hz:1≤S:= Fan.bloomT M H q hB z; have hh:1 ≤c := East.toll H D' hD z.1; have hZ:= pearlsNN M H L₁ hA z
    have hE:0 ≤ wife C₁ z.1 M z.2 P':= mul_nonneg (pow_nonneg (by unfold March.shiftG; positivity) _) (fareV ..); have hv:0 ≤ v:=mul_nonneg hZ hE
    by_cases hX: Height.tiredN H q z.1
    · let D:= Height.grow G L t; have hd:1 ≤D:= Real.one_le_rpow hB (by norm_num); let i:=z.1
      have hPos:1 ≤ Real.exp (Q.ε*Height.depth H i) := Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun i _=> H.positive_volume _))
      have ht':0≤Q.mark L μ t:= H.laws.acquired.marked
      have hM:1≤Real.exp (Q.mark L μ t*Height.overlap H i):=Real.one_le_exp (mul_nonneg ht' (Nat.cast_nonneg _))
      have hu : D^q ≤ S := by
        rcases hX with h|h|h
        · exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (by positivity) hM).trans
            (le_mul_of_one_le_right (by positivity) hPos))
        · exact hc.trans ((Real.exp_monotone (le_mul_of_one_le_right ht' (show (1:ℝ)≤ Height.overlap H i by exact_mod_cast h))).trans ((le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hd)).trans (le_mul_of_one_le_right (by positivity) hPos)))
        exact hcc.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hM)))
      exact (mul_le_mul_of_nonneg_right (hF.trans hu) hv).trans hg.2.1
    by_cases hp:∀ j i,i∈ (z.2 j).val→ A' i
    · by_cases hi:∀ j i, Sum.inl i∈ quietR M (z.1.snd j) (z.2 j)→ r₀ i ≤ n
      · exact (hR (Captain.canopy z.1 M z.2 q n r₀ A' hL hT _ ht hX h hp hi)).elim -- order
      push Not at hi; obtain ⟨j,i,hi,h'⟩:= hi
      have hT':waltz H χ M (z.1.2 j) (z.2 j) X≠0:=fun h=> ht (by unfold Captain.wingTerm; rw [Finset.prod_eq_zero (mem_univ j) h,mul_zero,zero_div])
      have hσ := Captain.silenced M _ _ X hT'
      have he': r≤ D' i:= hΥ i (hσ.2.2.2 _ hi) h'
      have ht:= East.toll_imp H D' hD z.1 i j (Finset.mem_sdiff.mp ((Finset.mem_preimage (hf:=LocalLTE.Fan.runOut (S:=_)|>.injOn)).1 hi)).1 -- edit
      exact (mul_le_mul_of_nonneg_right (he'.trans ht) hv).trans hg.2.2
    · push Not at hp
      have ht': r*pearl z.1 M L₁ z.2 ≤ pearl z.1 M rA z.2 := Fan.lance M H A' rA r aA L₁ ha hP hA hm z (by exact hp) -- order and Prop
      unfold wagesZ; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (ht'.trans (le_mul_of_one_le_left ((mul_nonneg hw hZ).trans ht') (one_le_mul_of_one_le_of_one_le hz hh))) hE -- edit
end
end YM.LocalLTE.Fan
