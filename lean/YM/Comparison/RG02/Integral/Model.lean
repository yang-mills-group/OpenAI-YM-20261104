import YM.Comparison.RG02.Actual.Charge
/-!
# Numerical model input and charging constants

Same marker coordinates as the expansion, actual group. This does *not* substitute a new law at
 failed indicators; from Role, require reconstruct actual density *separately* there. Need model
 here on full fields/y-axis as one continuation (t=0 never used at positive Eval). Envelope on
 full torus each entry for interchange proofs. Declare leading scalar outside kinetic logs, including
 volume-counting. Constants only fixed-period here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Integral
open Function Filter Finset MeasureTheory
open RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order YM.Next.SectorChange Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    {V : Type} [DecidableEq V] {R : Census V}

variable (K : Bulk.Kernel S p P O) {a A Λ : ℝ} {k : ℕ}
  (F : Forest S.ratio) (t : S.Choices)

@[fun_prop] lemma main_continuous_ell (h : P.Bounds p a A Λ) (i : Face (Per f)) : Continuous (fun U => P.ell U i) := by
  obtain ⟨F,hi,he⟩ := P.ell_dominated h i; unfold PathData.ell
  exact continuous_tsum (fun j=> by unfold PathData.ellTerms Slot.atSite expandAt; fun_prop) hi he

@[fun_prop] lemma main_continuous_atoms {T : ℕ → Atom G k} (ha : 0<a) (he : SumBudget (fun i↦ (T i).budget a) A) : Continuous (uncut T (n:=f)) := by
   have ht : Extra.Iteration.Charged T a A:=he
   unfold uncut; refine continuous_finsetSum _ fun i _=> ?_
   exact continuous_tsum (fun j => Atom.unmasked_cont ..) ((ht.absolute ha.le).mul_right _) (fun j U=> (T j).unmasked_bound U i)

lemma main_continuous_π (h : P.Bounds p a A Λ) : Continuous (mainTerm p P (n:=f)) ∧ Continuous (loop P (n:=f)) := by
   have ht (s : Signed) : Continuous (fun U:Config G f=> quadratic p P (pull s 0 U)) := by unfold quadratic faceValue; fun_prop (disch:=assumption)
   unfold mainTerm loop RG.Patch.average; constructor
   · exact continuous_const.mul (continuous_finsetSum _ fun i _=> ((ht i).add ((main_continuous_atoms h.width h.three).comp (continuous_pull i 0))).add ((main_continuous_atoms h.width h.four).comp (continuous_pull i 0)))
   exact continuous_const.mul (continuous_finsetSum _ fun i _=> (main_continuous_atoms h.width h.two).comp (continuous_pull i 0))

variable (g c₀ : ℝ) (U : Config G f) (V' : Config G c) (x : fieldDir G c 1)
    (W : Bulk.Colors R G f)

local notation "E" => Bulk.Joint S (G:=G) F
-- beta of fine coupling
def temperature (g : ℝ) := (g^2)⁻¹

def localClassic (p) (P:PathData G) := temperature g * (mainTerm p P U + W.vac g U)
def weight (p : Clip) (P:PathData G) := Real.exp (c₀ - localClassic g U W p P - loop P U)
-- mark kit uses powers of real-field coupling
def markedLog : Poly R := lit R (fun i=> (g ^ W.power i)⁻¹ • W.mark i g U)

variable [Fintype V] in
def model (_ : Bulk.Kernel S p P O) (x : Config G f) : Poly R := Complex.ofReal (weight g c₀ x W p P) • Poly.pass (markedLog g x W)

open YM.Next.Fluctuations.Sector in
lemma weight_formula :
   S.noise (temperature g) (S.prediction U t) V' = prefactor S G (temperature g) * Real.exp (- temperature g * noiseTaylor S V' U t) := by
   rw [YM.Push.BetaTransport.noise_factor]; unfold noiseTaylor YM.Push.BetaTransport.noiseEnergy YM.Push.BetaTransport.linkEnergy; rw [Finset.mul_sum]; rfl

variable (hW : Bulk.Well W)
include hW
lemma leaf_mark : Leaf.All (fun U=> markedLog g U W) := by
   unfold markedLog lit
   apply Leaf.sum; intro i; apply Leaf.insert_; simp_rw [Complex.real_smul]; exact (Leaf.multiply (Envelope.constC _) (hW.prices ..))

variable [Fintype V]
lemma leaf_model : Leaf.All (model g c₀ W K) := by
   obtain ⟨a,A,Λ,h⟩:= K.bounds
   obtain ⟨he,hb⟩:= main_continuous_π h (f:=f)
   apply Leaf.smul
   · exact Envelope.ofReal_env (Env.sub (Env.sub (Envelope.const _) ((Envelope.const _).mul ((Env.compact he).add (hW.envelope g)))) (Env.compact hb) |>.exp)
   refine Leaf.sum _ _ (fun i => ?_); exact Leaf.smul (Leaf.atom _) (Leaf.pow (leaf_mark g W hW) _)

lemma model_gauge : GaugeInvariant (model g c₀ W K) := by
  obtain ⟨a,A,Λ,h⟩:= K.bounds; intro t U; simp only [model,weight, localClassic,markedLog,Work.F05.mainTerm_gauge h, hW.natural g t U,Work.F05.loop_gauge h, show ∀ i, W.mark i g (gauge t U)=_ from (fun i=>hW.gauges i g t U)]
omit hW in
lemma model_unit : (model g c₀ W K U).part R.quiet = weight g c₀ U W p P := by rw [model,Poly.part_smul,markedLog,Poly.pass_part _ (part_lit_quiet _),mul_one]

end YM.Comparison.RG02.Integral
