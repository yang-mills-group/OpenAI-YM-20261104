import YM.Integration.WilsonRootedPhysicalCashCover

/-! Spatial reserve from the actual, lifted length of every inherited unmarked path.
One third of the given length price pays the derivative powers, and two thirds pays its physical cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalPathCover
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo
open Extra.Iteration WilsonStartup PhysicalNext PhysicalNext.Repeat Song
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {l : ℕ} (p : BudgetPoint) (A : ℕ→Atom G l)
variable {σ C Λ : ℝ}

def regularPoint (p : BudgetPoint) : BudgetPoint :=
  {p with supportExponent:=p.supportExponent+1,exponent_pos:=by linarith only [p.exponent_pos]}

lemma range (h : preExponent p / p.B ≤ σ/2) :
    preExponent (regularPoint p) / (regularPoint p).B ≤ 2*σ/3 := by
  have hb : 0<(p.B:ℝ):=Nat.cast_pos.mpr p.B_pos
  change (p.supportExponent+1+3)/p.B≤2*σ/3
  apply (div_le_iff₀ hb).mpr
  have h':= (div_le_iff₀ hb).mp h
  unfold preExponent at h'
  nlinarith only [h',p.exponent_pos]

variable (R : PathData G) {c : Clip}

private lemma high (β : ℝ) (he : 0<σ) (h : SumBudget (fun i=>(A i).budget σ) C) :
    SumBudget (fun i=>sine p A β i*Real.exp ((2*σ/3)*(A i).length)) (tenor G l p (2*σ/3) C β) := by
  let ρ:=2*σ/3
  let S:=turnFee p
  let D:=highFee G l p ρ
  have hρ : 0<ρ:=by dsimp [ρ];linarith
  have hs : 0≤S:=(turnFee_pos p).le
  have hD : 0≤D:=(Geo.highFee_pos G p l hρ).le
  let d:=p.threshold^l
  have hd : 0≤d:=pow_nonneg p.threshold_pos.le l
  refine budget_mono (Cost.scale (Cost.scale (Cost.scale h (D*d) (by positivity)) _ hs) |factor*β| (abs_nonneg _)) ?_ fun j=>?_
  · exact fun i=>mul_nonneg (sine_pos p A β i) (Real.exp_pos _).le
  unfold sine
  rw [mul_assoc,mul_assoc _ _ (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hs
  rw [Wages.scan, Atom.budget]
  let t:ℝ:=(A j).length
  have hz : 0≤t:=Nat.cast_nonneg _
  let g:=Wages.grade l p.power p.order
  let b:=Wages.startup G l p.power p.order
  let w:=(A j).magnitude
  change b*d*w*(t+1)^g*Real.exp (ρ*t)≤D*d*(w*Real.exp (σ*t))
  have hw : 0≤b*d*w:=mul_nonneg (mul_nonneg (show 0≤b by have hh:=Wages.slot_ge G p.power p.order 0;unfold b Wages.startup;positivity) hd) (by unfold w Atom.magnitude;positivity)
  rw [add_comm t]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (spendMoment g (half_pos hρ) hz) hw) (Real.exp_pos _).le).trans
  rw [show σ*t=ρ/2*t+ρ*t by dsimp [ρ];ring,Real.exp_add]
  change _≤b*momentPrice g _*_*_
  apply le_of_eq
  ring

private lemma low (hs : R.Bounds c σ C Λ) :
    SumBudget (fun d : Low => |d.mark R c| * lowCost G p (d.length R)*Real.exp ((2*σ/3)*d.length R))
      (lowFee G p (2*σ/3)*lowerSize c C) := by
  let ρ:=2*σ/3
  have hρ : 0<ρ:=by dsimp [ρ];linarith only [hs.width]
  apply Cost.mono (budget_scale (lowFee_nonneg G p hρ) (lower_budget G R hs))
  · exact fun i=>mul_nonneg (mul_nonneg (abs_nonneg _) (low_nonneg ..)) (Real.exp_pos _).le
  intro d
  let l:=d.length R
  have hi:=(low_vs G p l).trans (mul_le_mul_of_nonneg_left (spendMoment _ (half_pos hρ) (Nat.cast_nonneg _))
    (low_nonneg ..))
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (abs_nonneg (d.mark R c))) (Real.exp_pos _).le).trans
  rw [show σ*((d.length R):ℝ)=ρ/2*l+ρ*l by dsimp [l,ρ];ring,Real.exp_add,lowFee]
  unfold l ρ
  ring_nf
  rfl

private lemma pitchBook (β : ℝ) (h : SumBudget (fun i=>(A i).budget σ) C) (hs : 0<σ)
    (he : preExponent p / p.B≤2*σ/3) : Quotes.early p (pitch (n:=n) A) (fun i=>sine p A β i.2)
      (anchoredFee (headline p) (octave l)*tenor G l p (2*σ/3) C β) := by
  apply enhanced
  have half : (4*σ/3)/2=2*σ/3:=by ring
  refine Quotes.channel_mass (p:=headline p) (σ:=4*σ/3) (fun i=>(A i).length) (fun i=>(A i).footprint 0) _ (sine_pos p A β)
    (by simpa only [half] using high p A β hs h) (octave l) (he.trans_eq half.symm) ?_
  intro i
  have ht:=Wages.traversed (A i) (0:Site n) p.B p.B_pos
  change p.B*_≤p.B*octave l+_
  refine ht.trans ?_
  unfold octave
  nlinarith

private lemma lowBook (γ : ℝ) (h : R.Bounds c σ C Λ) (he : preExponent p / p.B≤2*σ/3) :
    Quotes.early p (fun i : Tally n=>strings R p (.inl i)) (fun i=>mezzo R c p γ i.2)
      (anchoredFee (headline p) lowCount*host G c p (2*σ/3) C γ) := by
  apply enhanced
  have half : (4*σ/3)/2=2*σ/3:=by ring
  apply Quotes.channel_mass (p:=headline p) (σ:=4*σ/3) (Low.length R) (fun i=>i.home R p (0:Site n)) _ (mezzo_pos R c p γ)
    _ lowCount (he.trans_eq half.symm) fun i=>low_geometry p R i _
  simp only [half]
  convert (Cost.scale (Cost.scale (low p R h) (turnFee p*p.threshold^2)
    (mul_nonneg (turnFee_pos _).le (sq_nonneg _))) |factor*γ| (abs_nonneg _)) using 2 with i
  unfold mezzo
  ring
  rfl

/-- The original full inherited reading, including the quadratic channel and all three translated
path families, is controlled at the raised cover exponent from the source's original half-width room. -/
theorem original (β γ : ℝ) (h : R.Bounds c σ C Λ) (hp : Decent c (regularPoint p))
    (he : preExponent p / p.B≤σ/2) :
    ∃f : Songbook n→ℝ,Quotes.early (regularPoint p) (strings R (regularPoint p)) f
      (octaveNeed G (regularPoint p) c (2*σ/3) C Λ β γ) ∧
      ∀i,(regularPoint p).Regular (strings R (regularPoint p) i).support (sounding R c β γ i) ∧
        (regularPoint p).supBounds (strings R (regularPoint p) i).site (strings R (regularPoint p) i).support
          (sounding R c β γ i) (f i) := by
  let q:=regularPoint p
  let f : Songbook n→ℝ:=Sum.elim (fun i=>mezzo R c q (-γ) i.2) (Sum.elim (fun i=>sine q R.cubic (-β) i.2)
    (Sum.elim (fun i=>sine q R.quartic (-β) i.2) (fun i=>sine q R.loop (-1) i.2)))
  have room:=range p he
  refine ⟨f,fun i=>?_,?_⟩
  · exact Cost.sum (lowBook q R (-γ) h room i) (Cost.sum (pitchBook q R.cubic (-β) h.three h.width room i)
      (Cost.sum (pitchBook q R.quartic (-β) h.four h.width room i) (pitchBook q R.loop (-1) h.two h.width room i)))
  · rintro (i|i|i|i)
    · exact tally_charge R c q i (-γ) hp
    · exact pitch_charge q _ i (-β) fun i=>(h.invariant i).2.1
    · exact pitch_charge q _ i (-β) fun i=>(h.invariant i).2.2
    · exact pitch_charge q _ i (-1) fun i=>(h.invariant i).1

end YM.Integration.WilsonRootedPhysicalPathCover
