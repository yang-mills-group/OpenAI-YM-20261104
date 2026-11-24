import YM.Integration.ManuscriptQLocalHardDisk
import YM.Integration.ManuscriptQLocalStandardTail

/-! The auxiliary axis acts on actual charged scalar occurrences of the incoming
regular slots and once on each already integrated hard component. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHardGraded
open Filter Function Finset Lattice RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Next.Scheduling AnalyticBridge VerifiedReset
open MergeProof Marker Extra.Multi LocalLTE PhysicalNext.Repeat.Daisy
open ManuscriptQLocalMarkedHeightTail
open scoped Classical Topology BigOperators

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ}
  {o:Target.Order G W} (H:Cash W x μ L Q o a T R)
variable {V ι:Type} [DecidableEq V] {Γ:Marker.Census V}

def tint (M:Menu.Hat Γ R) (ζ:ℂ) (d:ℕ) : Menu.Hat Γ R := {M with charge:=M.charge*ζ^d}

lemma circle (M:Menu.Hat Γ R) (ρ:ℝ) (d:ℕ) : tint M (ρ:ℂ) d=Menu.gradedHat M ρ d := rfl

lemma unscaled (M:Menu.Hat Γ R) (ρ:ℝ) : Menu.gradedHat M ρ 0=M := by
  cases M
  simp [Menu.gradedHat]

lemma scalar (M:Menu.Hat Γ R) (ζ:ℂ) (d:ℕ) : Menu.stamp (tint M ζ d)=ζ^d • Menu.stamp M := by
  unfold Menu.stamp tint
  rw [Menu.sent,mul_comm]

variable (M:ι→Menu.Hat Γ R) (ν:ι→ℕ)
private abbrev markedLeaves (row:ι→Menu.Hat Γ R) := fun i=>(row i).M
local notation "M₀"=>markedLeaves M

def ordinary (z:Fan.Stars H M₀) : ℕ := ∑v:Occ H M z,ν v.2.val

lemma factor (ζ:ℂ) (z:Fan.Stars H M₀) :
    matrix H (fun i=>tint (M i) ζ (ν i)) z=ζ^(ordinary H M ν z) • matrix H M z := by
  change (∏v:Occ H M z,Menu.stamp (tint (M v.2.val) ζ (ν v.2.val)))=_
  simp_rw [scalar]
  simp only [Finset.prod_smul,Finset.prod_pow_eq_pow_sum,ordinary,matrix]

def total (degree:Fan.Stars H M₀→ℕ) (h:ℕ) (z:Fan.Stars H M₀) : ℕ := h*degree z+ordinary H M ν z

def term (degree:Fan.Stars H M₀→ℕ) (h:ℕ) (ζ:ℂ) (z:Fan.Stars H M₀) : Poly Γ :=
  ζ^(h*degree z) • matrix H (fun i=>tint (M i) ζ (ν i)) z

lemma graded (degree:Fan.Stars H M₀→ℕ) (h:ℕ) (ζ:ℂ) (z:Fan.Stars H M₀) :
    term H M ν degree h ζ z=ζ^(total H M ν degree h z) • matrix H M z := by
  simp only [term,factor,smul_smul,←pow_add,total]

lemma physical (degree:Fan.Stars H M₀→ℕ) (h:ℕ) (z:Fan.Stars H M₀) :
    term H M ν degree h 1 z=matrix H M z := by rw [graded,one_pow,one_smul]

lemma exposure (degree:Fan.Stars H M₀→ℕ) (h:ℕ) (ζ:ℂ) (w:V→ℝ) (z:Fan.Stars H M₀) :
    Poly.price w (term H M ν degree h ζ z)=‖ζ‖^(total H M ν degree h z)*Poly.price w (matrix H M z) := by
  rw [graded,Poly.adapted,norm_pow]

theorem price_le {n:Side} {I : Type} {X : I → Support n} {M : ℕ} {α T : ℝ}
    {f g : I → ℝ} (h : Ac.Hit X M f α T) (hn : ∀ i, 0 ≤ g i)
    (hle : ∀ i, g i ≤ f i) : Ac.Hit X M g α T := by
  intro y
  apply budget_mono (h y)
  · intro i
    split
    · exact mul_nonneg (hn i) (Real.exp_nonneg _)
    · rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right (hle i) (Real.exp_nonneg _)
    · rfl

/-- Direct coefficient withdrawal in the original rooted absolute series.
Every monomial retained by the cut has at least the requested degree. -/
theorem leftover {n:Side} {I:Type} {X:I→Support n} {B:ℕ} {γ u ρ:ℝ} (hr:1≤ρ)
    (d:I→ℕ) (cost:I→ℝ) (hn:∀i,0≤cost i) (k:ℕ)
    (bought:Ac.Hit X B (fun i=>ρ^(d i)*cost i) γ u) :
    Ac.Hit X B (fun i=>if k≤d i then cost i else 0) γ ((ρ^k)⁻¹*u) := by
  have hp:0<ρ^k:=pow_pos (zero_lt_one.trans_le hr) _
  have hscale:=Quotes.hit_scale (inv_nonneg.mpr hp.le) bought
  apply price_le hscale
  · intro i;split <;> first | exact hn i | exact le_rfl
  · intro i
    by_cases hit:k≤d i
    · rw [if_pos hit]
      calc cost i=(ρ^k)⁻¹*(ρ^k*cost i):=by rw [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]
           _≤_:=mul_le_mul_of_nonneg_left
             (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr hit) (hn i)) (inv_nonneg.mpr hp.le)
    · rw [if_neg hit];exact mul_nonneg (inv_nonneg.mpr hp.le)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hr) _) (hn i))

lemma price_real {ρ:ℝ} (hr:0≤ρ) (w:V→ℝ) (z:Fan.Stars H M₀) :
    Poly.price w (matrix H (fun i=>Menu.gradedHat (M i) ρ (ν i)) z)=
      ρ^(ordinary H M ν z)*Poly.price w (matrix H M z) := by
  change Poly.price w (matrix H (fun i=>tint (M i) (ρ:ℂ) (ν i)) z)=_
  rw [factor,Poly.adapted,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]

variable {C d rv s A v y B e:ℝ} {j k:ℕ} {χ:Push.SectorMeasure.Chi}
  (N:Captain H j C d rv s A v y B e k χ)

theorem circle_price (w:V→ℝ) (hw:∀v,0<w v) {ρ:ℝ} (hr:0≤ρ) (h n:ℕ)
    (degree:Fan.Stars H M₀→ℕ) {γ u:ℝ}
    (sold:Ac.Hit (fun z:Fan.Stars H M₀=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ M₀ z then
        ρ^(h*degree z)*(Poly.price w (matrix H (fun i=>Menu.gradedHat (M i) ρ (ν i)) z)*
          Captain.wife N z.1 M₀ z.2 n) else 0) γ u) (ζ:ℂ) (hz:‖ζ‖≤ρ) :
    Ac.Hit (fun z:Fan.Stars H M₀=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ M₀ z then
        Poly.price w (term H M ν degree h ζ z)*Captain.wife N z.1 M₀ z.2 n else 0) γ u := by
  have wife (z:Fan.Stars H M₀) : 0≤Captain.wife N z.1 M₀ z.2 n:=
    mul_nonneg (pow_nonneg (by unfold March.shiftG;positivity) _) (Captain.fareV N z.1 M₀ z.2)
  apply price_le sold
  · intro z;split <;> first | exact mul_nonneg (Poly.nonnegative hw _) (wife z) | exact le_rfl
  · intro z
    by_cases live:0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ M₀ z
    · rw [if_pos live,if_pos live,exposure,price_real H M ν hr]
      calc _≤(ρ^(total H M ν degree h z)*Poly.price w (matrix H M z))*Captain.wife N z.1 M₀ z.2 n:=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg ζ) hz _) (Poly.nonnegative hw _)) (wife z)
           _=_:=by rw [total,pow_add];ring
    · rw [if_neg live,if_neg live]

theorem purchased_tail (w:V→ℝ) (hw:∀v,0<w v) {ρ:ℝ} (hr:1≤ρ) (h n:ℕ)
    (degree:Fan.Stars H M₀→ℕ) {γ u:ℝ}
    (sold:Ac.Hit (fun z:Fan.Stars H M₀=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ M₀ z then
        ρ^(h*degree z)*(Poly.price w (matrix H (fun i=>Menu.gradedHat (M i) ρ (ν i)) z)*
          Captain.wife N z.1 M₀ z.2 n) else 0) γ u) (cut:ℕ) :
    Ac.Hit (fun z:Fan.Stars H M₀=>Captain.reachability z.1) (radiusB x)
      (fun z=>if cut≤total H M ν degree h z then
        (if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ M₀ z then
          Poly.price w (matrix H M z)*Captain.wife N z.1 M₀ z.2 n else 0) else 0)
      γ ((ρ^cut)⁻¹*u) := by
  let cost (z:Fan.Stars H M₀):=if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H χ M₀ z then
    Poly.price w (matrix H M z)*Captain.wife N z.1 M₀ z.2 n else 0
  have pos:∀z,0≤cost z:=by
    intro z
    dsimp only [cost];split
    · exact mul_nonneg (Poly.nonnegative hw _) (mul_nonneg
        (pow_nonneg (by unfold March.shiftG;positivity) _) (Captain.fareV N z.1 M₀ z.2))
    · exact le_rfl
  have hρ:‖(ρ:ℂ)‖=ρ:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans hr)]
  have whole:=circle_price H M ν N w hw (zero_le_one.trans hr) h n degree sold (ρ:ℂ) hρ.le
  have bought:Ac.Hit (fun z:Fan.Stars H M₀=>Captain.reachability z.1) (radiusB x)
      (fun z=>ρ^(total H M ν degree h z)*cost z) γ u:=by
    simpa only [cost,mul_ite,mul_zero,exposure,hρ,mul_assoc] using whole
  exact leftover hr (total H M ν degree h) cost pos cut bought

end YM.Integration.ManuscriptQLocalHardGraded
