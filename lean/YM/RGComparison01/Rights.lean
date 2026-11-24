import YM.RGComparison01.Studio
/-!
# Common purchase grants for sponsors after blocks

 Keeps explicitly usable further auxiliary table on THIS Factor, Delay.
 Crossing exposed; threshold uniform in all i and β held. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Push.AbsoluteSums.Animals Slide Tensor WilsonStartup Bouquet Push.PriceCompiler
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves
open RG.Supply Shoot Input Org Ovens Progress.DirectedRecipe Next.Scheduling Further.PhysicalPeriodLimitF933
open Vision Studio
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {J : Targets X.p X.K}
  {E : Expenses J} {W : Return.Wages} {v : ℕ→ℝ}
  (R : PhysicalNext.Repeat.Register D E W v) (P : Sponsor G) {Θ : Protection D} (U : Delays Θ)
namespace Rights

-- meet at ANY apertures permitted. Lower support denormalization fees after caller.
def eta (j : ℕ) : ℝ:= ((j:ℝ)+1)⁻¹

def sky (C:Targets X.p X.K) (i j k : ℕ) (D:Rolls X.p) := escrow (C j i|>.halo) (P X D C i j k).stencil (High.countOrder (k+1))

structure Stock : Prop where
  asks (j:ℕ) (hh:4 ≤ j) i (hi:StepStages j i) k (ht:k ≤ j) (hk:1≤k): Nonempty (Studio.Workshops R P i j k hh (eta j) (U.betaEntry j))
  shell j i : StepStages j i → ∀ k ≤ j, Trio.maxFixed (sky P J i j k D) ≤ U.shells j ∧ 1 ≤ U.growth j
  start j i : (E j i).wanting=-(7/16:ℝ)

lemma upwards (j i:ℕ) (h : StepStages j i) : ∀ᶠ t:ℝ in atTop,∀ hV:4≤j,∀ k:Fin (j+1),1≤k.val→ Nonempty (Workshops R P i j k hV (eta j) t) := by
  by_cases hv: 4≤ j; swap; · simp [hv]
  have he (k:Fin (j+1)) : ∀ᶠ t:ℝ in atTop, 1≤k.val→ Nonempty (Workshops R P i j k hv (eta j) t) := by
    by_cases hM:1 ≤ k.val; swap; · simp [hM]
    obtain ⟨b,hb,hP⟩:= Studio.purchase R P i j k.val hv 0 (eta j) (by unfold eta; positivity) h hM
    exact (eventually_ge_atTop b).mono (fun t ht hp=> hP _ ht)
  exact (eventually_all.mpr he).mono fun t hk _=> hk

private lemma uniforms (g : ℕ → ℕ → ℕ) (V : Delays Θ):∃ W:Delays Θ,DelayLe V W∧∀ X : Delays Θ, DelayLe W X → ∀ j i,StepStages j i → g j i≤ X.shells j ∧ 1 ≤ X.growth j:= by
  refine ⟨{V with shells:=fun i=> V.shells i+fromMax g i,growth:=fun i=> V.growth i+1},⟨le_rfl,le_rfl,fun i=> Nat.le_add_right ..,fun i=> Nat.le_succ _⟩,fun W h j i hi=>?_⟩
  exact ⟨((le_fromMax g hi).trans (Nat.le_add_left (fromMax g j) _)).trans (h.shells j),(Nat.le_add_left 1 _).trans (h.growth j)⟩
private lemma race (U:Delays Θ) (g:ℕ→ℕ→ℕ→ℕ) (F:ℕ→ℕ→ℝ→Prop) (h : ∀ j i, StepStages j i → ∀ᶠ x:ℝ in atTop,F j i x) : ∃ V:Delays Θ, DelayLe U V ∧∀ Z : Delays Θ, DelayLe V Z → (∀ j i,StepStages j i → F j i (Z.betaEntry j)) ∧ ∀ j i,StepStages j i → ∀ k≤j,g j i k ≤ Z.shells j ∧ 1 ≤ Z.growth j := by
  let v j i:= (Finset.univ:Finset (Fin (j+1))).sup (fun k=>g j i k.val)
  obtain ⟨V,hV,hT⟩:= uniforms v U
  obtain ⟨x,-,hu,hX⟩:= collect_upper V.betaEntry _ fun j=>eventually_transitions j _ _ fun i hi=> h j i hi
  let Z : Delays Θ:= {V with betaEntry:=x}; have hx : DelayLe V Z:=⟨hu,le_rfl,le_rfl,le_rfl⟩; refine ⟨Z,hV.trans hx,fun W h=> ⟨fun j i hi => hX j _ (h.beta j) i hi,fun j i hi k hk=>?_⟩⟩
  obtain ⟨h₁,h₂⟩:= hT W (hx.trans h) j i hi; let z : Fin (j+1):= ⟨k,by omega⟩; exact ⟨le_trans (Finset.le_sup (f:=fun p:Fin (j+1)=>g j i p.val) (mem_univ z)) h₁,h₂⟩
lemma negotiate (hs : ∀ i j, (E i j).wanting=-(7/16:ℝ)) : ∃ V:Delays Θ, DelayLe U V ∧ ∀ W : Delays Θ,DelayLe V W→ Stock R P W := by
  obtain ⟨X,hX,H⟩:= race U (fun j i k=> Trio.maxFixed (sky P J i j k D)) (fun j i x=>∀ hV:4≤j,∀ k:Fin (j+1),1≤k.val→ Nonempty (Workshops R P i j k hV (eta j) x)) (upwards R P)
  refine ⟨X,hX,fun V h=> ⟨fun j hv i he k hk ht=> (H V h).1 j i he hv (⟨k,by omega⟩ : Fin (j+1)) ht,(H V h).2,hs⟩⟩

variable {A : Alloy X D} (F : Roost.Factor A)

def wants (P : Sponsor G) : Agenda G := fun _ _ _ _ _ _ _ _ _ _ R _ _ _ _ _ _ U=> Stock R P U
lemma payable : (wants P).Payable := by
  intro s T V z X E h; exact ⟨fun i=>0,fun L hL D v w R F S P' p Q hp θ V=> Rights.negotiate (X:= UVExtension.Case.provider s T L) R P V (fun i j=> (h i j).2.2.2.1)⟩

variable (hp:(wants P).atFactor F) {i n k : ℕ}
local notation "J₀" => A.B.a.clock.J (i+1)
local notation "I₀" => A.B.a.clock.J i
local notation "B" => radiusB (A.B.a.clock.hatBeta i)
include hp
lemma stands (hk:k≤J₀):
    let h:= sky P F.target I₀ J₀ k D
    2*Trio.base h B < (A.B.a.S.side i n).val ∧ 4*Meadow.studio h B+16≤ (A.B.a.S.side i n).val := by
  intro h
  have H := A.B.valid.volume i n; obtain ⟨h',hv⟩:= (show Stock F.shape P A.delay from hp).shell _ _ (step_paid A.B.a i) k hk
  have he: 0 < Trio.maxFixed h:=by unfold Trio.maxFixed Trio.base Trio.tent; omega
  have hR: 2*Trio.base h B < (A.B.a.S.side i n).val:= by
    apply lt_of_lt_of_le _ H; let u:= A.B.a.clock.coverSize (i+1); let j:= J₀
    change _ < A.delay.shells j*(1+B+u)^_
    apply lt_of_le_of_lt (Trio.roof h _ (A.B.a.budget i).B_pos); refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_right _ (show Trio.maxFixed h ≤ A.delay.shells j from h'))
    apply Nat.mul_lt_mul_of_pos_left _ he; exact lt_of_lt_of_le (b:=1+B+u) (by change B < _; omega) (le_self_pow₀ (by omega) (by omega))
  exact ⟨hR,(by unfold Trio.base Trio.tent at hR; omega)⟩
end Rights
end YM.RGComparison01
