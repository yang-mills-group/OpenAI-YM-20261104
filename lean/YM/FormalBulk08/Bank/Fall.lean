import YM.FormalBulk08.Bank.Vol

/-! Goal: exact one-step recurrence on all-orders formal action,
before kinetic substitution, with regulator Kith check; preserve for limit
continuation in output level. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {V : Type*} {I : Type*} {J : Type*}
variable {G : Gauge} {K : KernelChoices} {P : Patch} {j t : ℕ} (U : Flight j t) (F : Lodge U.patch) (W : Pot G) (ρ : ChartRatio G)

def coastRight (C I J : Type*) (v:C ×J) : C ×(I⊕J) := (v.1,Sum.inr v.2)
lemma saddle_right (n : Side) (K : KernelChoices) (a:wire G n): saddleP G (primary U.patch K n) F (Sum.inr a)= coastRight _ _ _ a := rfl
variable (h : U.patch.Branches K G)
def magma := swim (lands (rayshot U F h)) (cola W ρ U F K)
def coastRun : Pot G := fun e r=> ∑ i∈Finset.range (3*e+1),jetty (coastRight _ _ _) (magma U F W ρ h i e r)
def whirl (n:Side) (k : (primary U.patch K n).Choices): Waves (Tor n (BoardL G U.patch F)) := swim ((rayshot U F h).acts n) (rancho (coffer W ρ U F h n k))
def whirled (n:Side) (k : (primary U.patch K n).Choices) (e r : ℕ) := ∑ i∈Finset.range (3*e+1), jetty (coastRight _ _ _) (whirl U F W ρ h n k i e r)
lemma read_tor (hr : LocalRatio ρ) (hp : Story W (pink K.penalty U.wing)) {s C : ℝ} (hs : 0<s) (hC:0≤C) (hu : (Flight.duo K.penalty U).A0.strip s C) (n : Side) (k : (primary U.patch K n).Choices) (ht : 4≤t) (e r):
    rancho (landed U ρ h F n k (stone W (n*U.patch.L))) (e+1) r=whirled U F W ρ h n k (e+1) r := by
    let T:= primary U.patch K n; let H:= ferry U h F n;let E:=saddleP G T F; let p:= flush (Reef.floor K U F n) k ρ (Mesa.stone W _);
    let A:=rancho (cobalt H p);let B:= rancho (coffer W ρ U F h n k)
    have hf : Fiery A:=bath_vac U F W ρ h n k hp.toVivid hr hs hC hu
    obtain ⟨η,C,hη,hc,h₁,-⟩:= colors G K.penalty K.penalty_pos U.legal
    have hx := consolidate U ρ h F n hr k (Mesa.stone W _) (stoned_main hη.le hc.le (h₁ U.wing).1 hp.toVivid hp.ink _) ht
    change marble _ (coeff _ (out H p))=_; rw [extraction H p hx A rfl hf]; unfold whirled; apply Finset.sum_congr rfl; intro i hi
    have hz : ∀ a b,A a b=jetty E (B a b):= fun a b=> infer_joust E _ _ _
    rw [← dye_swim E (aqua H.saddle) ((rayshot U F h).acts n) (ray_forms U F h n) B A hz];rfl
lemma sailed_val (hp : Vivid W) (ht : LocalRatio ρ) : Fiery (coastRun U F W ρ h):=by
   intro e r ht'; unfold coastRun at ht'; by_contra hh; refine ht' (Finset.sum_eq_zero fun i hi=> ?_)
   have he : magma U F W ρ h i e r=0:= by by_contra he;obtain ⟨hx,hA,hK,-⟩:= thermal _ (fairy W ρ U F K hp ht) _ _ _ he; exact hh ⟨hx,hA,hK⟩
   rw [he];rfl
lemma sailed_fin (hp : Vivid W) (hr : LocalRatio ρ) {s C : ℝ} (hs:0<s)(hc:0≤C) (hx : (Flight.duo K.penalty U).A0.strip s C) (n : Side) (k : (primary U.patch K n).Choices) : Fiery (whirled U F W ρ h n k) := by
   intro e r ht; unfold whirled at ht; by_contra hh; refine ht (Finset.sum_eq_zero fun i hi=>?_)
   have he : whirl U F W ρ h n k i e r=0:= by by_contra he;obtain ⟨hx,hl,hK,-⟩:= thermal _ (fiat U F W ρ h n k hp hr hs hc hx) _ _ _ he; exact hh ⟨hx,hl,hK⟩
   rw [he];rfl
end YM.FormalBulk08.Bank
