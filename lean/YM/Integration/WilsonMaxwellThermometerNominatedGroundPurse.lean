import YM.Integration.WilsonMaxwellThermometerNominatedProperFaces
import YM.Integration.WilsonMaxwellThermometerNominatedDeltaProper

/-! The comparison table is the single physical Maxwell prescription on the
original separated compact set. Its inverse weights are bounded before the
cutoff, original period, and fields are sampled. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundPurse
open Finset Filter Function Set Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE Table Spec Extraction Trace Trace.Pilot PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Rose
open Marker QuadraticLocal Extra.Trajectories Primitives.GCC.Anchor
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerNominatedProperFaces WilsonMaxwellThermometerNominatedDelta
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "J₀" => Stock.census (Fin 3)

def table (p:Badge→ℂ):Poly J₀:=Poly.inject fun s=>if s=(J₀).quiet then 1 else p s.val
def policy (x:Points 3):Poly J₀:=table (ground R x)

theorem unit (p:Badge→ℂ):(table p).part (J₀).quiet=1:=by
  change (if (J₀).quiet=(J₀).quiet then (1:ℂ) else p (J₀).quiet.val)=1
  rw [if_pos rfl]

private theorem size (p:Badge→ℂ) {c:ℝ} (hc:1≤c) (v:∀s,‖p s‖≤c):
    rent (table p)≤8*c:=by
  unfold rent Poly.price
  calc
    _≤∑s:(J₀).Mode,c:=by
      apply Finset.sum_le_sum
      intro s _
      change Poly.toll (fun _:Fin 3=>1) s*‖(if s=(J₀).quiet then (1:ℂ) else p s.val)‖≤c
      by_cases h:s=(J₀).quiet
      · simpa [Poly.toll,h] using hc
      · simpa [Poly.toll,h] using v s.val
    _=_:=by
      have n:Fintype.card (J₀).Mode=8:=by decide
      rw [Finset.sum_const,Finset.card_univ,n,nsmul_eq_mul]
      norm_num

theorem inverse (W:Poly J₀) (qu:W.part (J₀).quiet=1):
    inverseMass W=1+(1-W)+(1-W)^2+(1-W)^3:=by
  let X:=1-W
  have nil:X^4=0:=Poly.stops X (by simp [X,sub_eq_add_neg,qu]) 4 (by decide)
  have prod:W*(1+X+X^2+X^3)=1:=by
    calc
      W*(1+X+X^2+X^3)=(1-X)*(1+X+X^2+X^3):=by simp [X]
      _=1-X^4:=by ring
      _=1:=by rw [nil,sub_zero]
  calc
    inverseMass W=inverseMass W*(W*(1+X+X^2+X^3)):=by rw [prod,mul_one]
    _=(W*inverseMass W)*(1+X+X^2+X^3):=by ring
    _=_:=by rw [right_inverse qu,one_mul]

def gross (a:ℝ):ℝ:=1+(1+a)+(1+a)^2+(1+a)^3

private theorem purchase (W:Poly J₀) (qu:W.part (J₀).quiet=1) {a:ℝ} (bill:rent W≤a):
    rent (inverseMass W)≤gross a:=by
  let X:=1-W
  have neg:rent (-W)=rent W:=by simp [rent,Poly.price]
  have one:rent (1:Poly J₀)=1:=Poly.one_price
  have wx:rent X≤1+a:=by
    have add:=Poly.addition (fun _:Fin 3=>zero_lt_one) (1:Poly J₀) (-W)
    change rent X≤rent (1:Poly J₀)+rent (-W) at add
    rw [neg,one] at add
    exact add.trans (add_le_add (le_refl 1) bill)
  have non:0≤rent X:=Poly.nonnegative (fun _:Fin 3=>zero_lt_one) X
  have pow (n:ℕ):rent (X^n)≤(1+a)^n:=(Poly.powers (fun _:Fin 3=>zero_lt_one) X n).trans (pow_le_pow_left₀ non wx n)
  have add (P Q:Poly J₀):rent (P+Q)≤rent P+rent Q:=Poly.addition (fun _:Fin 3=>zero_lt_one) P Q
  rw [inverse W qu]
  exact (add _ _).trans (add_le_add ((add _ _).trans (add_le_add ((add _ _).trans (add_le_add one.le wx)) (pow 2))) (pow 3))

theorem budget {E:Set (Points 3)} (compact:IsCompact E) (legal:E⊆conf 3):
    ∃B:ℝ,1≤B ∧ ∀x∈E,rent (inverseMass (policy R x))≤B:=by
  have h (s:Badge):∃b:ℝ,∀x∈E,‖ground R x s‖≤b:=by
    have cont:ContinuousOn (fun x=>‖ground R x s‖) E:=fun x hx=>
      (WickGoal_tied (C:=R.family) (source R.family s) (legal hx)).continuousAt.norm.continuousWithinAt
    obtain ⟨b,h⟩:=(compact.image_of_continuousOn cont).bddAbove
    exact ⟨b,fun x hx=>h ⟨x,hx,rfl⟩⟩
  choose b hb using h
  let C:=1+∑s:Badge,|b s|
  have c₁:1≤C:=le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>abs_nonneg _)
  have all (x:Points 3) (hx:x∈E) (s:Badge):‖ground R x s‖≤C:=by
    have h:=Finset.single_le_sum (fun (i:Badge) (_:i∈Finset.univ)=>abs_nonneg (b i)) (Finset.mem_univ s)
    exact ((hb s x hx).trans (le_abs_self _)).trans (by dsimp [C];linarith)
  refine ⟨max 1 (gross (8*C)),le_max_left _ _,?_⟩
  intro x hx
  exact (purchase _ (unit _) (size _ c₁ (all x hx))).trans (le_max_right ..)

end YM.Integration.WilsonMaxwellThermometerNominatedGroundPurse
