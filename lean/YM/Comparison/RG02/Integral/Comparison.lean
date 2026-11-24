import YM.Comparison.RG02.Integral.Window
/-!
# Exact one-step local expansion at any external log input

 The real side uses (temperature g) in `StepData.Push`; later specialize to actual coupling of
 Rep. K & W not an analytic continuation of that Rep; W from independently rendered input
 germs. Exact algebraic extraction with chosen windows, **distinguished** error items. No norms
 on RG remainder supplied by this file. The statement `compare` is one possible complete density
 numerator/denominator identity (full marker in one), *not* claiming that the actual weight
 is approximated by a single absolute-error polynomial! Use only with local/log/relative budget
 estimates e.g. by regrouping before costing in large volume. Outside disk seam, the flagged data
 still enter. The next modules exposit their actual pieces and leading vacuum on valid masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Integral
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order YM.Next.SectorChange Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (g c₀ : ℝ) (x : fieldDir G c 1) (W : Bulk.Colors R G f)
local notation "I" => Precision.Key F G
local notation "Y" => F.Slice G
local notation "V'"=> sample g x
local notation "dγ" => Gaussian.cloud (K.covariance F t)
local notation "L"=> (I→ℝ)

variable (A : Set (F.Slice G)) (D : Lit R (Config G f))

-- Inside model `ambient`, standardized by charge against thermal fluctuations; `desired` polynomial full-Gaussian moments (outside windows).
def desired (r : ℕ) : Lit R L := fun v=>Assembly.evaluated W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) r (g:ℂ) (Bulk.translated K F x v)
variable (r : ℕ)
lemma desired_cost : Good dγ (desired K F t g x W r) ∧ charge dγ (desired K F t g x W r)= Order.value (g:ℂ) (Bulk.Fk K F t W x r) := by
   have ht:= Assembly.moment_integral (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) (K.covariance F t) (K.symm F t) (K.positive F t) r (g:ℂ)
   exact ⟨fun s=>(ht s).1, Poly.ext fun i=>(ht i).2.symm⟩

local notation "U"=> dγ
local notation "St" => Actual.stack t V' (temperature g)
local notation "P'" => model g c₀ W K
local notation "dA" => scope K F g x A
local notation "F'"=> desired K F t g x W r

-- Error menu, prefix not included. Leave explicit for estimates,
-- also for genuine remoteness/seam partitions up to a representative norm consumer.
def drift : Lit R L := (dA).indicator (ambient K F t g x W - F')
def removed : Lit R L := (dA)ᶜ.indicator F'
def olderInput : Lit R (Config G f) := D-P'
def older : Lit R Y := A.indicator (St (olderInput K g c₀ W D) ∘ F.drape)
def outside : Lit R Y := Aᶜ.indicator (St D ∘ F.drape)

def shortage := Complex.ofReal (wage K F t g c₀ x) • (charge dγ (drift K F t g x W A r)- charge dγ (removed K F t g x W A r)) +
      charge (F.order G) (older K F t g c₀ x W A D)+ charge (F.order G) (outside F t g x A D)

variable (h : Trust K F t g x A) (hg : 0<g) (H : Bulk.Well W) (hs : Leaf.All D)
include h
include hg H in
lemma drifted : Good dγ (drift K F t g x W A r) := by
   have HI := identity K F t g 0 x W A h hg H
   unfold drift
   rw [Set.indicator_sub']; exact HI.1.sub ((desired_cost K F t g x W r).1.on_window (scope_meas K F g x A h.seen.1))
lemma removable : Good dγ (removed K F t g x W A r) := (desired_cost ..).1.on_window (scope_meas K F g x A h.seen.1 |>.compl)
include hs H in
lemma heritage : Good (F.order G) (older K F t g c₀ x W A D) := (good_slice F t V' (temperature g) K.branches (leaf_sub hs (leaf_model K g c₀ W H))).on_window h.seen.1
include hs in
omit [Fintype V] in
lemma outer : Good (F.order G) (outside F t g x A D) := (good_slice F t V' (temperature g) K.branches hs).on_window h.seen.1.compl

include H hg in
lemma one_thermal : charge (F.order G) (A.indicator (St P' ∘ F.drape))= Complex.ofReal (wage K F t g c₀ x) • (Order.value (g:ℂ) (Bulk.Fk K F t W x r) + charge dγ (drift K F t g x W A r) - charge dγ (removed K F t g x W A r)) := by
   rw [(identity K F t g c₀ x W A h hg H).2,← (desired_cost K F t g x W r).2]; congr 1
   unfold drift removed; let R' := ambient K F t g x W
   have he:= scope_meas K F g x A h.seen.1
   rw [Set.indicator_sub', Actual.sub_cost (identity K F t g c₀ x W A h hg H).1 ((desired_cost K F t g x W r).1.on_window he),split_cost (desired_cost K F t g x W r).1 he]; abel

include H hg hs
lemma tag_charge (hy : GaugeInvariant D) : charge (prior G f) (St D)=Complex.ofReal (wage K F t g c₀ x) • Order.value (g:ℂ) (Bulk.Fk K F t W x r)+shortage K F t g c₀ x W A D r := by
   rw [pack F t _ _ K.branches hs hy]; rw [split_cost (good_slice F t _ _ K.branches hs) h.seen.1]
   have he : A.indicator (St D ∘ F.drape) = A.indicator (St P' ∘ F.drape) + older K F t g c₀ x W A D := by
       unfold older; rw [← Set.indicator_add']; congr 1; ext1 y; unfold Actual.stack Function.comp olderInput; simp only [Pi.sub_apply,Pi.add_apply,smul_sub]; abel
   rw [he,add_cost ((good_slice F t _ _ K.branches (leaf_model K g c₀ W H)).on_window h.seen.1) (heritage K F t g c₀ x W A D h H hs),one_thermal K F t g c₀ x W A r h hg H]; unfold shortage outside; rw [smul_sub,smul_add,smul_sub]; abel

omit h
def leftover (r : ℕ) (A : S.Choices → Set (F.Slice G)) := ∑ u:S.Choices, shortage K F u g c₀ x W (A u) D r

-- full unnormalized moment in **given g external units** (extend group link logs as periodic).
-- Need `x` and `V'` each time. Choose `t` arbitrarily for the reference once (note: proves Fk
-- independent of t, no such assertion for physical cost). This Poly is NOT trimmed in marks.
lemma compare (A : S.Choices→Set (F.Slice G)) (Hu : ∀ u, Trust K F u g x (A u)) (hy : GaugeInvariant D) :
    Actual.Push S (temperature g) D (sample g x) = Complex.ofReal (office K F t g c₀ x) • Order.value (g:ℂ) (Bulk.Fk K F t W x r) + leftover K F g c₀ x W D r A := by
   rw [agreed _ _ K.branches hs]; simp_rw [fun u=> tag_charge K F u g c₀ x W (A u) D r (Hu u) hg H hs hy,sum_add_distrib]
   unfold leftover; congr 1
   let b:= Order.value (g:ℂ) (Bulk.Fk K F t W x r)
   have ht u : wage K F u g c₀ x=wage K F t g c₀ x := by unfold wage; rw [office_choice K F u _ _ _ t]
   have he := show (count S:ℂ) ≠ 0 from by exact_mod_cast (count_pos (S:=S)).ne'
   calc
     _= (∑ _i:S.Choices, Complex.ofReal (wage K F t g c₀ x)) • b := by
         rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun i _=> by rw [ht i, Bulk.fkChoice K F i W x r t]
     _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,wage, Complex.ofReal_div,Complex.ofReal_natCast,mul_comm]; exact congrArg (· • b) (div_mul_cancel₀ _ he)
end YM.Comparison.RG02.Integral
