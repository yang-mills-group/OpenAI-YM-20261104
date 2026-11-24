import YM.Integration.WilsonVacuumPreResetCurvatureField

/-! Length-weighted original derivative bounds for the exact quadratic,
cubic and quartic source. A common hard-sector or loop bill is not needed
when truncating these separate signed curvature terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvaturePrice
open Function Filter Finset Lattice RG Wilson Precision Exterior Matrix
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes
open Next.Scheduling Extra.Iteration Song Meadow WilsonStartup Geo
open WilsonVacuumPreResetCurvatureField
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}

def cost (B:BudgetPoint)(c:Clip)(σ C γ β:ℝ):ℝ:=
  anchoredFee (headline B) lowCount*host G c B σ C γ+
    (anchoredFee (headline B) (octave 3)*tenor G 3 B σ C β+
      anchoredFee (headline B) (octave 4)*tenor G 4 B σ C β)

theorem original (B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (clip:Decent c B)(reach:preExponent B/B.B≤σ/4)(γ β:ℝ):
    ∃ f:Rows n → ℝ,early B (fun i=>strings K B (slot i))
       (fun i=>f i*Real.exp (σ/4*arc K (slot i))) (cost (G:=G) B c σ C γ β) ∧
    ∀i,B.Regular (strings K B (slot i)).support (source K c γ β i) ∧
      B.supBounds (strings K B (slot i)).site (strings K B (slot i)).support
        (source K c γ β i) (f i):=by
  let f:Rows n → ℝ:=Sum.elim (fun i:Tally n=>mezzo K c B γ i.2)
    (Sum.elim (fun i:Stave (n:=n)=>sine B K.cubic β i.2)
      (fun i:Stave (n:=n)=>sine B K.quartic β i.2))
  have low:early B (fun i:Tally n=>strings K B (.inl i))
      (fun i=>mezzo K c B γ i.2*Real.exp (σ/4*i.2.length K))
      (anchoredFee (headline B) lowCount*host G c B σ C γ):=by
    apply enhanced
    refine Quotes.channel_mass (p:=headline B) (Low.length K) (fun i=>i.home K B (0:Site n))
      (fun i:Low=>mezzo K c B γ i*Real.exp (σ/4*i.length K))
      (fun i=>mul_nonneg (mezzo_pos ..) (Real.exp_nonneg _)) (σ:=σ/2) ?_ lowCount
      (by rw [div_div];norm_num;exact reach) (fun i=>low_geometry B K i _)
    convert (Cost.scale (Cost.scale (low_budget G B K h) (turnFee B*B.threshold^2)
      (mul_nonneg (turnFee_pos _).le (sq_nonneg _))) |VerifiedReset.factor*γ| (abs_nonneg _)) using 2 with i
    rw [mul_assoc (Song.mezzo ..),←Real.exp_add]
    unfold mezzo
    ring_nf
    rfl
  refine ⟨f,fun x=>Cost.sum (low x) (Cost.sum (torque B _ h.three h.width reach β x) (torque B _ h.four h.width reach β x)),?_⟩
  rintro (i|i|i)
  · exact tally_charge K c B i γ clip
  · exact pitch_charge B _ i β (fun j=>(h.invariant j).2.1)
  · exact pitch_charge B _ i β (fun j=>(h.invariant j).2.2)

theorem long (B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (clip:Decent c B)(reach:preExponent B/B.B≤σ/4)(γ β:ℝ)(D:ℕ):
    ∃ f:Rows n → ℝ,early B (fun i=>strings K B (slot i))
       (fun i=>if D≤arc K (slot i) then f i else 0)
       (Real.exp (-(σ/4)*D)*cost (G:=G) B c σ C γ β) ∧
      ∀i,B.Regular (strings K B (slot i)).support (source K c γ β i) ∧
        B.supBounds (strings K B (slot i)).site (strings K B (slot i)).support
          (source K c γ β i) (f i):=by
  obtain ⟨f,paid,rows⟩:=original (n:=n) B K c h clip reach γ β
  refine ⟨f,?_,rows⟩
  exact arch_tail (k:=D) _ B _ paid (div_nonneg h.width.le (by norm_num)) (fun i=>(rows i).2.1)

end YM.Integration.WilsonVacuumPreResetCurvaturePrice
