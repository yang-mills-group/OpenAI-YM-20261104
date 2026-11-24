import YM.Comparison.RG02.Integral.Model
/-!
# Numerical equality of model integrands with thermal transform

 Pointwise on *mouth* with fitted likelihood. All temperature and volume scale included. Use
 one t of the full joint tag (counting measure); not repeating orientation likelihood per factor.
 `calorie` includes the *full quadratic* coarse term w/ x dependence; Expand before resetting
 from that. No t-estimate asserted about contributions where this transform isn't used, or cost of
 log division etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Integral
open Function Filter Finset MeasureTheory
open RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order YM.Next.SectorChange Actual
open PertExtension.Series YM.Next.Fluctuations.Sector
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    {V : Type} [DecidableEq V] {R : Census V}

variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)

variable (g c₀ : ℝ) (x : fieldDir G c 1) (W : Bulk.Colors R G f)
local notation "E" => Bulk.Joint S (G:=G) F
local notation "I" => Precision.Key F G
local notation "Y" => F.Slice G
local notation "w"=> prefactor S G (temperature g)
local notation "T" => temperature g
local notation "L"=> (I→ℝ)
def count (S : StepData c f) := Fintype.card S.Choices
lemma count_pos : 0 < count S:= Fintype.card_pos

def tab := O.scale^(Fintype.card F.Free)
def calorie := Real.exp (c₀ - Bulk.infrared S p P F t (K.b F) x)
-- heat of leading quadratic fixed on THIS space, and counters

def standard := tab (F:=F) (O:=O)*w*calorie K F t c₀ x

def office := chartCost (K.covariance F t) g * standard K F t g c₀ x
-- one tag, without heuristics independent importance. `common` scaled. Uniform reference weight.
def one_tag := standard K F t g c₀ x / count S

def wage := office K F t g c₀ x / count S
lemma wage_pos (hg : 0<g) : 0<wage K F t g c₀ x := by
   have := prefactor_pos (G:=G) (S:=S) T
   have := K.ratio.scale; have := chartCost_pos _ (K.positive F t) hg
   have := count_pos (S:=S)
   unfold wage office standard tab calorie
   positivity
lemma standard_pos : 0<standard K F t g c₀ x := mul_pos (mul_pos (pow_pos K.ratio.scale _) (prefactor_pos _)) (Real.exp_pos _)
lemma office_pos (hg : 0<g) : 0<office K F t g c₀ x := mul_pos (chartCost_pos _ (K.positive F t) hg) (standard_pos ..)
lemma tag_pos : 0<one_tag K F t g c₀ x := div_pos (standard_pos ..) (Nat.cast_pos.mpr count_pos)
lemma paid_as : wage K F t g c₀ x=chartCost (K.covariance F t) g * one_tag K F t g c₀ x := mul_div_assoc ..

lemma office_choice (t' : S.Choices) : office K F t g c₀ x=office K F t' g c₀ x := by
   unfold office standard calorie; rw [K.convention F t t']; unfold Bulk.infrared Assembly.jet
   have he : Bulk.Surface S p P F t =ᶠ[𝓝 0] Bulk.Surface S p P F t':= Work.F04.tested_germ K.branches F p P t t'
   rw [(he.iteratedFDeriv ℝ 2).eq_of_nhds]

-- real relative log chart. `translated` in Poly Fk.
def sample := represent (g • x)
def repSample : Y := fun i=> replica S.ratio (sample (c:=c) g x) i

def offset (v : L) := g • (fderiv ℝ (K.b F) 0 x + tape v)
def walk (v : L) := release (repSample F g x) (offset K F g x v)
def start : L := g • tape.symm (fderiv ℝ (K.b F) 0 x)

lemma displaced_eq (v : L) : displaced (start K F g x) g v=offset K F g x v := by
  let z:= fderiv ℝ (K.b F) 0 x
  unfold displaced offset start; change gaugeCount (g • gaugeCount.symm z+g • v)=g • (z+gaugeCount v)
  rw [map_add,map_smul,map_smul,gaugeCount.apply_symm_apply,smul_add]

local notation "ζ" => Bulk.translated K F x
lemma ribbon_eq (v : L) : g • (ζ v) =(g, (g • x), offset K F g x v) := by
   apply Prod.ext
   · simp only [Bulk.footing]; exact mul_one g
   simp_rw [Bulk.footing]; rfl
lemma fine_eq (v : L) : F.drape (walk K F g x v)=Work.F03.live F (g • (ζ v)).2 := by rw [ribbon_eq]; rfl
lemma stone_eq (v : L) : Bulk.stone F t K (g • (ζ v))=mainTerm p P (F.drape (walk K F g x v))+noiseTaylor S (sample g x) (F.drape (walk K F g x v)) t := by
  rw [ribbon_eq]; rfl

lemma chart_costs (v : L) : pay O (offset K F g x v)=tab (F:=F) (O:=O)*∏ i,O.J (offset K F g x v i) := by unfold pay tab; simp [Finset.prod_mul_distrib]
lemma pays_exp (v : L) (ha : offset K F g x v ∈ mouth O) : pay O (offset K F g x v)=tab (F:=F) (O:=O)*Real.exp (Real.log (∏ i,O.J (offset K F g x v i))) := by
  rw [chart_costs,Real.exp_log (Finset.prod_pos (fun i _=> K.ratio.pos _ (ha i (Set.mem_univ _))))]
lemma numerator_mark (v : L) : markedLog g (F.drape (walk K F g x v)) W = Assembly.smoothMark W.power (Bulk.markFn S F W) g (ζ v) := by rw [fine_eq]; unfold markedLog Assembly.smoothMark; simp_rw [Assembly.divided,Bulk.markFn,Bulk.posed,ribbon_eq]

-- prove completed shape equality with thermal weighting, on valid log branch

lemma completed_cost (v : L) (hg : 0<g) (hW : Bulk.Well W) :
    c₀-Bulk.infrared S p P F t (K.b F) x + Radial.higher (Bulk.geometric K F t W) g (ζ v)=
      let U := F.drape (walk K F g x v)
      let β := temperature g
      let J := sample g x
      let a := offset K F g x v
      Gaussian.force (K.covariance F t) v/2+Real.log (∏ i, O.J (a i)) - β * noiseTaylor S J U t +
        (c₀ - β*(mainTerm p P U+ W.vac g U) - loop P U) := by
    dsimp only
    have he := Bulk.completed K F t W x v hW
    unfold Radial.higher; rw [← Assembly.jet_eq, he,Bulk.geometric,stone_eq]
    unfold Bulk.fee
    let U := F.drape (walk K F g x v)
    have hp : Bulk.pillar (F:=F) (g • (ζ v))=g^2:= by rw [ribbon_eq]; rfl
    have hv : Bulk.officer F K (g • (ζ v))= loop P U - Real.log (∏ i, O.J (offset K F g x v i)) := by rw [ribbon_eq]; rfl
    have hx : Bulk.supplement S F W (g • (ζ v))= W.vac g U := by rw [ribbon_eq]; rfl
    rw [hp,hv,hx]
    unfold U temperature; field_simp; ring

variable [Fintype V]

def ambient : Lit R L := fun z=> Assembly.numeric W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) g (ζ z)
-- probability inter-level noise cofactor, complete quadratic extraction
-- scalar check
private lemma reorder {a b c d e r y z X Υ Z:ℝ} (h : a+b=c+d-e*r+y) :
    Real.exp c*(X*Real.exp d)*(Υ*(Z * Real.exp (-e*r))*Real.exp y)*z =
    Υ*(X*Z*Real.exp a) * Real.exp b*z := by
    rw [show -e*r=-(e*r) by ring]; have he:= congrArg Real.exp h
    rw [sub_eq_add_neg] at he; simp_rw [Real.exp_add] at he; linear_combination -(Υ*X*Z*z)*he

-- keep likelihood generally, apply uniform weight on actual Good windows only later.
omit [Fintype V] in
lemma actual_weight (v : L) (h : 0<g) (hw : Bulk.Well W) (hm : offset K F g x v∈mouth O) :
    let u := F.drape (walk K F g x v)
    let V' := sample g x
    Real.exp (Gaussian.force (K.covariance F t) v / 2) * pay O (offset K F g x v) *
        (taggedKernel S (temperature g) t u V'* weight g c₀ u W p P) =
      (S.likelihood u t * standard K F t g c₀ x) * Real.exp (Radial.higher (Bulk.geometric K F t W) g (ζ v)) := by
   dsimp only; unfold taggedKernel
   rw [pays_exp K F g x v hm, weight_formula]
   simpa only [weight, standard, calorie, localClassic,mul_one] using reorder (z:=1) (Υ:=S.likelihood (F.drape (walk K F g x v)) t) (X:=tab (F:=F) (O:=O)) (Z:=w) (completed_cost K F t g c₀ x W v h hw)
lemma actual_model (v : L) (h : 0<g) (hw : Bulk.Well W) (hm : offset K F g x v∈mouth O) :
    let u := F.drape (walk K F g x v)
    Complex.ofReal (Real.exp (Gaussian.force (K.covariance F t) v / 2) * pay O (offset K F g x v)) •
        Actual.stack t (sample g x) (temperature g) (model g c₀ W K) u =
      Complex.ofReal (S.likelihood u t * standard K F t g c₀ x) • ambient K F t g x W v := by
   dsimp only; unfold stack model; rw [numerator_mark]; unfold ambient Assembly.numeric
   rw [Poly.product_bead]; simp_rw [smul_smul,← Complex.ofReal_mul]; rw [actual_weight K F t g c₀ x W v h hw hm]
end YM.Comparison.RG02.Integral
