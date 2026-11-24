import YM.OPE.Compatible.Grout.Hedges
import YM.Next.SCHEDULE.Support
/-!
 # Generalize within-one-scale receipts to variable gap. Adapt from Weigh: anchor→hit. E orbit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open Next.Scheduling (decay decay_summable)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m : ℕ} {W a r t σ E Λ μ x κ w C s ε: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
def est (p:BudgetPoint)(ε:ℝ):= (12*(p.B+1):ℝ)^(4:ℕ) * ∑' i, decay 4 ε i
lemma perceive {ι : Type} {u : ι→ RegularAddress f} {w : ι→ℝ} {a : ℝ} (he:0<ε) (hP:t+ε ≤ p.supportExponent)(h : ∀ i, 0≤w i)
    (hh:∀ x : Site f,SumBudget (fun i=> if (u i).site=x then p.mass (u i).support (w i) else 0) a) : Ac.Hit (fun i => (u i).support) p.B w t (est p ε * a) := by
  let B:=p.B
  let d i:= coverNumber B (u i).support
  let Φ (r : ℕ) := r*(4*B+2)+2*B
  let q (x : Site f) i := if (u i).site=x then p.mass (u i).support (w i) else 0
  let z : ℝ := 12*(B+1); have hZ : 0≤z := by unfold z; positivity
  have ha:=budget_nonneg (hh 0)
  intro x
  let F i := if x ∈ (u i).support then w i*Real.exp (t*d i) else 0
  have ht i : 0≤ F i := by unfold F; split; exact mul_nonneg (h i) (Real.exp_pos _).le; rfl
  have hd : SumBudget (decay 4 ε) (∑' i, decay 4 ε i) := ⟨fun i => by unfold decay; positivity,decay_summable _ _ he,le_rfl⟩
  let L := est p ε * a
  have hr : L=(z^4*a) * ∑' i, decay 4 ε i := by unfold L est z B; ring
  change SumBudget F L
  rw [hr]; apply budget_fiberwise d ht _ (budget_scale (mul_nonneg (pow_nonneg hZ 4) ha) hd)
  intro i U hU
  let s:=halo (Φ i) {x}; let g:=Real.exp (-ε*i)
  have he j (hj : j∈U) : F j≤g * ∑ y∈s,q y j := by
    unfold F; split
    next hx =>
      have hl : (u j).site∈s := halo_spec.mpr ⟨x,mem_singleton_self _,?hh⟩
      case hh => rw [← hU j hj]; exact Corona.extent _ _ hx (u j).anchor
      apply le_trans (b:=g * q (u j).site j) _ (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun y=>q y j) (fun y _ => (hh y).1 j) hl) (Real.exp_pos _).le)
      unfold q; rw [if_pos rfl]; change _ ≤ Real.exp _ * (Real.exp (p.supportExponent*d j)*_)
      rw [hU j hj,←mul_assoc,← Real.exp_add, mul_comm (w j)]; apply mul_le_mul_of_nonneg_right _ (h j); apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_right hP (show 0 ≤ (i:ℝ) by positivity)]
    exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun y _ => (hh y).1 _)
  have hk : (s.card:ℝ) ≤ z^4*((i:ℝ)+1)^ (4:ℕ) := by
    have he := Corona.halo_size {x} (Φ i); rw [card_singleton, one_mul] at he
    apply (show (s.card:ℝ) ≤ (↑((Φ i+Φ i+1)^4:ℕ):ℝ) by exact_mod_cast he).trans
    rw [←mul_pow]; dsimp only [Φ,z]; push_cast; gcongr; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) (Nat.cast_nonneg (α:=ℝ) B)]
  calc
    ∑ j∈U,F j ≤ ∑ j∈U,_ := sum_le_sum he
    _ = g*∑ y∈s,∑ j∈U,q y j := by rw [← mul_sum,sum_comm]
    _ ≤ g*∑ _y∈s, a := mul_le_mul_of_nonneg_left (sum_le_sum (fun y _ => budget_sum (hh y) _)) (Real.exp_pos _).le
    _ = g*((s.card:ℝ)*a) := by simp
    _ ≤ g*(z^4*((i:ℝ)+1)^ (4:ℕ)*a) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk ha) (Real.exp_pos _).le
    _ = _ := by unfold g decay; ring
variable {J:Seats F} {X:Support f} {ι:Type} [Countable ι]
local notation "Atlas_" => Config G f → ℝ
lemma one_collection {Z : ι→Support f}{v:ι→Atlas_}{k:ι→ℝ}(h:FoldsGrip F J X) (hp : ∀ i, Paced R (Z i) S (v i) (k i))(hv: ∀ U:Config G f,Summable (fun i=>v i U)) (hk:Ac.Hit Z R.p.B k a W):
     Sable R S X a (tweak J (fun U=>∑' i,v i U)) (2*(X.card*W)) := by
   let f i:= tweak J (v i);let t:={b:ι// f b≠0}
   let m i:=coverNumber R.p.B (Z (i:t).val)
   have hx(i:t):= trouble h (hp i.val) i.property
   have hf:t→ι:=Subtype.val; clear hf
   refine ⟨t,inferInstance,fun i=> f i.val,m,_,hx,?_,fun i=>?_⟩
   · have ht:=budget_over X _ _ (fun i _hi=> hk i)
     rw [sum_const,nsmul_eq_mul] at ht; apply budget_mono (budget_pull (fun i:t=>i.val) Subtype.val_injective (budget_scale zero_le_two ht))
     · intro i; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg zero_le_two (hp i.val).safe)
     intro i; obtain ⟨j,hj,hJ⟩ := Finset.not_disjoint_iff.mp (struckNear h (hp i.val) i.property)
     have he:= Finset.single_le_sum (f:=fun p=>if p∈Z i.val then k i.val * Real.exp (a*m i) else 0) (fun j _=> (hk j).1 i.val) hj
     rw [if_pos hJ] at he
     exact le_trans (le_of_eq (by ring : Real.exp (a*(m i:ℝ))*(2*k i.val)= 2*(k i.val*Real.exp (a*m i)))) (mul_le_mul_of_nonneg_left he zero_le_two)
   have he: HasSum (fun v=>f v i) _:= (hv i).hasSum.sub (hv (razed J i)).hasSum
   exact (Subtype.val_injective.hasSum_iff (f:=fun v=>f v i) (fun k hk=> by rw [show f k=0 from by by_contra H; exact hk ⟨⟨k,H⟩,rfl⟩]; rfl)).mpr he
end YM.PhysicalNext.Repeat.Aroma
