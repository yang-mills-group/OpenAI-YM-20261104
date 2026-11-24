import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Meets
import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Teacher
/-! # Continuum correlations and OPE coefficients in the measured frame

The bounds assume calibration of the measured coupling and the compact comparison
`supplies_round`. Truncation uses the measured coupling at each radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

variable {n h z : ℕ} {d:Fin n→ℕ} (hd:∀ i, d i ≤ z) (hh:h≤z)
    {A:Set (Points n)} {L:ℝ} (hA:IsCompact A)(hx:A⊆conf n) (hL:0≤L)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "e" => fun (_:Fin 1)=>h
local notation "g" => g0 G
local notation "B" => GroupS.gaugeN N.scheme N.criterion O ν
-- per compact pair, a fixed W may always be used in buying all Round & G6. Publish book
-- kept through each cap at H_r. Consumer doesn't depend on cover regulator.
def supplies_round (F:Final C f S) (Z:ℝ→tower S) (V:Arenas G) (t:ℝ→ℝ) :=
    ∀ {n m z:ℕ} (d:Fin n→ℕ) (y:Fin m→ℕ) (A:Set (Points n)) (E:Set (Points m)) (hd:∀ i,d i ≤ z)(hz:∀ i,y i≤z),
    IsCompact A→ A⊆conf n→ IsCompact E→ E⊆Outside m→ ∀ᶠ W:ℝ in atTop,∀ b:ℝ,0<b→∀ p:ℕ,
      Round V t (measures F Z d y) hd hz p 1 b W A E

variable (S0: StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
    (p:ℕ) (pay : Calibrated G t) (X : supplies_round F Z (Scale.Measure.outlook N.scheme N.criterion) t)
include H hZ hQ S0 pay X hA hx hL hd hh
lemma through (hn:0<n) : ∃ C : ℝ, 0<C ∧ ∀ᶠ r in late,
    ∀ x∈A,∀ o:Owner F,∀ u∈Balls L G d,
      tallyZ (numbers (coefficients F Z Q d h o r x u - purchaseMS N ν O u x h p (t r))) ≤ C * |t r|^(p+1) := by
  obtain ⟨M,hM,δ,hδ,L0⟩:= arbitrarily_large hA hx (isCompact_singleton (x:=RootG)) (singleton_subset_iff.mpr ok_wall)
  obtain ⟨W,⟨hW,hF,hw⟩,hx,hy⟩:= (L0.and ((X d e A {RootG} hd (fun _=>hh) hA hx isCompact_singleton (singleton_subset_iff.mpr ok_wall)).and
    (X e e {(0:Points 1)} {RootG} (fun _=>hh) (fun _=>hh) isCompact_singleton (singleton_subset_iff.mpr (injective_of_subsingleton _)) isCompact_singleton
      (singleton_subset_iff.mpr ok_wall)))).exists
  obtain ⟨B',hB,u⟩ := ((eventually_ge_atTop L).and (sufficiently (G:=G) (h:=h))).exists
  obtain ⟨b,hb,y⟩:= (M4 F Z Q H hZ hQ pay S0 hd hh hW hA (by assumption) hn u (hL.trans hB) hM hδ hw hF (p+1) p le_rfl (1/2) (by norm_num) (by norm_num)).exists
  obtain ⟨q,h⟩:= y.exists
  obtain ⟨C,hC,H⟩:= h 1 1 zero_lt_one le_rfl (hx b hb q) (hy b hb q)
  refine ⟨C*2^(p+1),by positivity,?_⟩
  have he : ∀ᶠ r in late, g r ≤ 2*|t r| := by
    filter_upwards [(show Tendsto _ _ _ from pay).eventually_const_lt (show (1:ℝ)/2<1 by norm_num), coupling_payment sim pay,g0_pos sim] with r hi hv hp
    rw [abs_of_pos hv.1]; replace hi := (lt_div_iff₀ hp).mp hi; linarith
  filter_upwards [H,ample sim 1 zero_lt_one W b hb,he,g0_pos sim] with r H h he hi x hx o u hu
  rw [ ← cropMS N ν O (by assumption)]; specialize H _ h le_rfl le_rfl o x hx u (fun i b=>(hu i b).trans hB)
  exact H.2.2.2.trans (by rw [mul_assoc,←mul_pow]; gcongr)

-- take T=W sufficiently large but constant, Far empty for single-scale comparison.
-- resulting tariff has no aperture growth. Use even all actual viewers.
omit H hZ hQ S0 pay X hA hx hL hd hh
private abbrev qd := fun _ : Fin 0=>0
private lemma freeGone {p:Points 0} : p∈Outside 0:= by change Injective (α:=Fin 1) _; exact injective_of_subsingleton _
private lemma filled (x:Points n) (y:Points 0) : forest x y=x:= by
  ext1 i; change (points _).ofLp i=_; change (forest x y).ofLp (Fin.castAdd 0 i)=_; rw [forest_left]
private lemma answer_empty (v:Slots G d) (w:Slots G qd) (o:Owner F) (x:Points n) (s T:ℝ) (hs:0<s) (y:Points 0) (hx:x∈conf n) :
    total F Z d qd o s T x y v w=moment (spectator F o.1) (atPosition o.2 s x.ofLp) (enter Z s v) := by
  rw [total_eq]; refine zero_far _ _ (spectate ..) _ _ _ ?_; intro i j he; exact hx (smul_right_injective _ hs.ne' (add_left_cancel (show _=_ from he)))
include hd in
private lemma answer_read (V:Arenas G)(B':ℝ→Frames G)(v:Slots G d)(w: Slots G qd)(x:Points n)(y:Points 0)(s:ℝ)(hx:x∈conf n)(he:∀ i,qd i ≤ z) :
    measurement V B' hd he x y s v w = PowerSeries.mk (fun k=> V z n ⟨x,hx⟩ k (liftSlots hd v)) := by
  ext1 k; rw [measurement,PowerSeries.coeff_mk, inserted_apply, vacant_tally, Finset.sum_singleton,bareRow_apply,Finsupp.single_eq_same,filled x y]; change kernel V z x k _ = _; rw [PowerSeries.coeff_mk,kernel_on V hx]; apply congr_arg; funext i
  exact Fin.append_left ..
include H hZ hQ S0 pay X hA hx hL hd
lemma correlation : ∃ C:ℝ,0<C ∧ ∀ᶠ r in late,∀ x ∈ A,∀ u∈Balls L G d,∀ o:Owner F,
    ∀ q:x∈conf n,
      ‖moment (spectator F o.1) (atPosition o.2 r x.ofLp) (enter Z r u) - crop p (t r)
        (PowerSeries.mk (fun k=> convertedMS N ν O z n ⟨x,q⟩ k (liftSlots hd u)))‖ ≤ C*|t r|^(p+1) := by
  -- use first-line also, T fixed but to the right of every clearance
  obtain ⟨M,hM,δ,hδ,R⟩:= arbitrarily_large hA hx (isCompact_singleton (x:=(0:Points 0))) (singleton_subset_iff.mpr freeGone)
  let q:Fin 1→ℕ:=fun _=>z; have he : ∀ i,qd i ≤ z:= fun i=>i.elim0
  obtain ⟨W,⟨hW,hw,v⟩,h1,h2⟩:= (R.and ((X d qd _ {(0:Points 0)} hd he hA hx isCompact_singleton (singleton_subset_iff.mpr freeGone)).and (X q qd {(0:Points 1)} {(0:Points 0)} (fun _=>le_rfl) he isCompact_singleton (singleton_subset_iff.mpr (injective_of_subsingleton _)) isCompact_singleton (singleton_subset_iff.mpr freeGone)))).exists
  obtain ⟨C,hC,q₁,Z'⟩:= Original.first F Z N ν O H d qd hd he (le_refl z) hL hA hx isCompact_singleton (singleton_subset_iff.mpr freeGone) hW v pay p
    (b:=1) ⟨milestone Z H W hW zero_lt_one (transition sim pay) S0,h1 1 zero_lt_one p,h2 1 zero_lt_one p⟩
  let K:=(1+Real.log W)^q₁; have H' : 0 < K := by unfold K; have hz:= Real.log_nonneg hW; positivity
  let w : Slots G qd := fun i=> i.elim0
  refine ⟨(C*K)*2^(p+1),by positivity,?_⟩
  filter_upwards [Z',ample sim 1 zero_lt_one W 1 zero_lt_one, (show Tendsto _ _ _ from pay).eventually_const_lt (show (1:ℝ)/2<1 by norm_num), coupling_payment sim pay,g0_pos sim,self_mem_nhdsWithin] with r hr Z' H₀ c l u x hx v hv o Hx
  have hp:= hr _ (le_refl W) Z' x hx (0 : Points 0) (Set.mem_singleton _) o v hv w (fun i=> i.elim0)
  have hp:= (le_add_of_nonneg_right (opPos _)).trans hp
  rw [answer_empty F Z _ _ o x r W u _ Hx,answer_read hd _ _ _ _ _ _ _ Hx] at hp
  rw [MSbook N ν O H] at hp
  have hj : ∑ i,qd i=0:=by simp
  apply hp.trans
  rw [hj, pow_zero,one_mul]; let a:=g r; have V: a ≤ 2*|t r| := by rw [abs_of_pos c.1]; have d: (1:ℝ)/2*a < t r:= (lt_div_iff₀ l).mp H₀; linarith
  change C*(a^(p+1))*K ≤ _; rw [mul_assoc (C*K),← mul_pow,mul_right_comm]; gcongr
end YM.FVA2.GradedFar259.Original
