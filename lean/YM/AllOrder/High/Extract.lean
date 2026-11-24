import YM.AllOrder.High.Skirt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir

/-!
# Preservation of POINTWISE additive log including indicator partners

After support shifts of the general all-order stratum (Eber). One output basis
per step, all FAllowed; this will also work whenever the finite family chosen
(for the step under β, period etc) is paired to the others by Offers. Doesn't
apply mask merger yet. Generalizes first-order template.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "B" => radiusB p
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)


open Trio Slide -- edit
variable (F:Finset H.fragrances) (χ:Chi) (p':BudgetPoint)
section ledgerT
variable {γ t v:ℝ} (hp:Collection.Local (posting p' H) p' (plusone H (Match.staple (H:=H) (J:=H) rfl rfl rfl) χ γ) t v)
include hp
lemma spared (V:Config G c) :
    (posting p' H|>.read (plusone H Θ χ γ)|>.additive p' V) = (Beam.marquee H p'|>.read (leftover F χ k γ)|>.additive p' V) +
       ∑ i∈foliage F k, masked p'.threshold ((Beam.marquee H p').reg i).support ((plusone H Θ χ γ).logRead i) V:= by
  let t' i:= masked p'.threshold ((Beam.marquee H p').reg i).support ((plusone H Θ χ γ).logRead i) V; let h i:=if i∈ foliage F k then t' i else 0
  let f i:= ((posting p' H).read (plusone H Θ χ γ)).regularOccurrence p' i V; let g i:= ((Beam.marquee H p').read (leftover F χ k γ)).regularOccurrence p' i V
  have he : g=f-h:= by
    funext i; change masked _ _ ((leftover F χ k γ).logRead i) V=f i-h i; rw [ledger]; have hh : f i=t' i:= by unfold t'; rw [Beam.rewrite_rule]; rfl
    rw [hh]; unfold h; split
    next hz=> rw [sub_self]; simp [masked]
    next hz=> rw [sub_zero]; rfl
  have hs: Summable f:= Roof.Embrasure.series _ _ hp V
  have h':HasSum h (∑ i∈ foliage F k,t' i):=by
    convert hasSum_sum_of_ne_finset_zero (s:= foliage F k) (f:=h) (fun i hi=> if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
    infer_instance
  have he': (∑' i, g i)= (∑' i, f i)-∑ i∈ foliage F k,t' i:= by rw [he]; exact (hs.hasSum.sub h').tsum_eq
  change (∑' i,f i)=(∑' i, g i)+_; rw [he',sub_add_cancel]
variable {β v₀ C L E : ℝ} {Y : BudgetPoint}
local notation "λ₀" => (leftover F χ k γ)
local notation "P₀" => (posting p' H)
lemma chants (V:Config G c) (hR:R=Pane.virgin T Y β)
    (ht:S.push β R.eval V=earlyValue (P₀) T.down T.low p' (plusone H Θ χ γ) β v₀ γ V) (h':T.down.Bounds T.low C L E)
    (hh:flags p'.threshold V=∅): Token.arrayE T Y β γ V= v₀*(Fintype.card (Site c):ℝ)- (∑ x, chamber F χ k γ x V) - ∑' i, (λ₀).logRead i V:= by
  -- get ht
  let D i:= (λ₀).logRead i V; have hK : ∑ i∈foliage F k, masked p'.threshold ((Beam.marquee H p').reg i).support ((plusone H Θ χ γ).logRead i) V=
      ∑ x, chamber F χ k γ x V := by
    simp_rw [bound_frame F χ p' γ, Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i hi
    rw [← Finset.sum_mul, Meadow.paysOne,one_mul]; exact masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
  have hx : (Beam.marquee H p'|>.read (λ₀)|>.additive p' V)= ∑' i, D i:= tsum_congr fun i=> masked_eq _ _ _ _ (by unfold Healthy; rw [hh]; simp)
  unfold Token.arrayE; rw [← hR,ht]; have hg : ((P₀).read (plusone H Θ χ γ)).gas p' V=1:= Activities.gas_one _ _ hh; have hf: Collection.receipt T.down T.low p' V= secondTerm T.low T.down V:= VerifiedReset.allGoodPrice h' V hh
  unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only; rw [hg,mul_one, ← Real.exp_add,Real.log_exp, Pane.crystalline _ _ _ _ _ hh, hf, spared F χ p' hp,hK,hx]; change _= _ -∑' i,D i; ring
end ledgerT
section income
variable (γ:ℝ) {Y:Stars→Side} {w r:ℕ} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa:∀ i:Stars,Offer G (Y i)) (V:Config G c)
local notation "P₀" => (Beam.marquee H p')
local notation "h₀" => (plusone H Θ χ γ)
local notation "h₁" => (leftover F χ k γ)
local notation "R₀" => foliage F k
local notation "f₀" => chamber F χ k γ
def used (k:ℕ) (i:Site c) (V:Config G c):= ∑ x∈foliage F k, Meadow.garnerAt H p' i x *((P₀).read h₀|>.regularOccurrence p' x V)
def occasion (k:ℕ) (i:Site c) (V:Config G c) := used F χ p' γ k i V - chamber F χ k γ i 1 - unearned p' Q z (Trio.rip fa) i V
lemma levyG (t C : ℝ) (h : Collection.Local (posting p' H) p' h₀ t C):
    ((posting p' H).read h₀).additive p' V=(P₀|>.read h₁|>.additive p' V) + (Fintype.card (Site c):ℝ)* f₀ 0 1 + (∑ i:Site c, masked p'.threshold (neighbors z i) (ornament Q fa i) V) + ∑ i, occasion F χ p' γ Q z fa k i V:= by
  let f:= f₀ 0 1; have hp i: f₀ i 1=f:= by
    rw [show i= Lattice.affine 1 i (0:Site c) from (by simp [Lattice.affine]), ← turns F χ k γ 0 1 i 1]; rw [pull_one]; change f₀ 0 (Lattice.translate i 1)=_; rfl
  rw [spared F χ p' h]; let v i:= used F χ p' γ k i V
  have he: ∑ i∈R₀,masked p'.threshold ((Beam.marquee H p').reg i).support ((h₀).logRead i) V=∑ x:Site c,v x:= by
    unfold v used; rw [sum_comm]; symm; refine sum_congr rfl ?_; intro i hi; rw [← sum_mul,Meadow.paysOne,one_mul]; rfl
  rw [he]; unfold ornament; rw [Trio.parade]; simp_rw [occasion,hp]; rw [sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul, card_univ]; unfold v f; ring
variable (hBod:p'.B=Pressure.radiusB p) (hc0 : ∀ i∈F,∀ x∈perf H i,perf H i⊆neighbors r x) (hop : Pressure.radiusB p + Pressure.radiusB p ≤ r) (u:Site c)
include hc0 hop hBod
variable {sf c' : ℝ} (h : Collection.Local (posting p' H) p' (plusone H (Match.staple (H:=H) (J:=H) rfl rfl rfl) χ γ) sf c')
include h
open Boulevard
lemma liftsG : ‖used F χ p' γ k u V‖ ≤ (ballCost r:ℝ)*sf:= by
  obtain ⟨a,ha,hX⟩:= h.cheap
  let Z:= B; let P':= posting p' H; let f i:= masked p'.threshold (P'.reg i).support (((P₀).read (plusone H Θ χ γ)).E i) V
  let R i:= Meadow.garnerAt H p' u i; have hv i : ((P₀).read h₀|>.regularOccurrence p' i V)= f i:= by change masked _ ((P₀).reg i).support _ _=_; rw [Beam.rewrite_rule]
  unfold used; simp_rw [hv]; apply le_trans (norm_sum_le ..)
  let s:= neighbors r u; let E i x:= if (P'.reg i).site=x then a i * Real.exp (preExponent p' * coverNumber p'.B (P'.reg i).support) else 0
  calc
    _ ≤ ∑ i∈ R₀, ∑ x∈s,E i x:= by
        apply sum_le_sum; intro i hi; have hp : 0≤∑ x∈s,E i x:=sum_nonneg fun x _=> (hX x).1 i
        change ‖R i*f i‖ ≤ _; by_cases ht:R i=0; · rw [ht,zero_mul,norm_zero]; exact hp
        have he:= (artists F p' hBod hc0 hop u i hi ht).2; rw [Beam.rewrite_rule] at he
        rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg (f i)) (Meadow.portions ..)).trans; apply (CouplingShape.mask_cost (ha i) V).trans
        apply (le_mul_of_one_le_right (ha i|>.1) (Real.one_le_exp (show 0≤preExponent p' * coverNumber p'.B (P'.reg i).support from mul_nonneg (Song.headline p').exponent_pos.le (Nat.cast_nonneg _)))).trans;
        unfold E; rw [sum_ite_eq,if_pos (he (P'.reg i).anchor)]
    _ ≤ (ballCost r:ℝ)*sf:= by
        rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hX x) R₀))
        rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) h.H_nonneg
lemma chamber_value (hU: flags p'.threshold V=∅): ‖f₀ u V‖ ≤ (ballCost r:ℝ)*sf:= by
  have he i : ((P₀).read h₀|>.regularOccurrence p' i V)=((h₀).logRead i) V:= masked_eq _ _ _ _ (by unfold Healthy; rw [hU]; simp)
  have hp:= liftsG (k:=k) F χ p' γ V hBod hc0 hop u h; unfold used at hp; simp_rw [he] at hp
  rw [(bound_frame F χ p' γ u), Finset.sum_apply]; exact hp
lemma early_cloud (f : Stars→ℝ) (hq:∀ i (V:Config G (Y i)), flags p'.threshold V=∅→∀ x, ‖fa i x V‖ ≤ f i) (hp:w+4 ≤ z) : ‖occasion F χ p' γ Q z fa k u V‖ ≤ (ballCost r:ℝ)*sf +(ballCost r:ℝ)*sf +∑ i:Stars,|ray i| * ((Fintype.card (Site (Y i)):ℝ)*(f i+f i)) := by
  apply (norm_sub_le ..).trans; apply add_le_add ?_ (Trio.stipends p' V Q z fa _ hq hp u)
  exact (norm_sub_le ..).trans (add_le_add (liftsG F χ p' γ V hBod hc0 hop _ h) (chamber_value F χ p' γ 1 hBod hc0 hop u h (Boulevard.smoky («P»:=p') (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using p'.threshold_pos))))
omit h
variable {l:ℕ} (hq : ∀ i,p'.Regular ((posting p' H).reg i).support ((plusone H (Match.staple (H:=H) (J:=H) rfl rfl rfl) χ γ).logRead i))
    (hP : ∀ i j, p'.Regular univ (fa i j))
include hq hP
lemma tidy_occasion (hp:w+4 ≤z) (he:r ≤ l) (hk : 2*z ≤ l) : Tidy p' (neighbors l u) (occasion F χ p' γ Q z fa k u):= by
  let V i := Trio.unearned p' Q z (rip fa) u i
  refine tidy_sub p' (v:=V) (u:= used F χ p' γ k u - fun _ : Config G c=> f₀ u 1) ?_ ?_
  · apply tidy_sub _ _ (tidy_const ..)
    refine tidy_sum _ _ R₀ _ fun i hi=> ?_; by_cases hB: Meadow.garnerAt H p' u i=0; · simp only [hB,zero_mul]; exact tidy_const ..
    refine tidy_scale _ _ (tidy_mask _ (X:=((P₀).reg i).support) ?_ ?_)
    · rw [Beam.rewrite_rule]; exact hq i
    intro j hj; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((artists F p' hBod hc0 hop u i hi hB).2 hj)).trans he
  refine tidy_sum _ _ _ _ fun i _=> tidy_scale _ _ (tidy_sum _ _ _ _ fun j _=> tidy_mask _ (unit_m p' Q z fa hP hp (emerge Q i j u) i j) (Trio.patch Q z hp i j u hk)) -- pattern
omit hq hP
variable {V}
lemma occasion_none (s:Site c) (hz:2*z≤l) (hw:w+4≤z) (hp:2*r≤ w) (hc:4*r+16≤c.val) (hT:0<r) (h : CompatibleP p' r f₀ fa) (hV: Healthy p'.threshold (neighbors l s) V): occasion F χ p' γ Q z fa k s V=0:= by
  have he := tinted (f₀) fa h
  have hk : used F χ p' γ k s V=f₀ s V:= by
    unfold used; rw [bound_frame F χ p' γ s, Finset.sum_apply]; refine sum_congr rfl ?_; intro i hi
    let A:= (Beam.marquee H p').reg i; let Q':= (h₀).logRead i
    by_cases hx:Meadow.garnerAt H p' s i=0; · rw [hx]; simp
    have hv:= artists F p' hBod hc0 hop s i hi hx; have hΩ : Healthy p'.threshold A.support V:= hV.mono_left (fun p he=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (hv.2 he)).trans (by omega)))
    exact congr_arg (Meadow.garnerAt H p' s i * ·) (masked_eq _ _ Q' V hΩ)
  have hh := Trio.cruising p' Q z (rip fa) V s hw hp hz hc hV _ he ((by omega))
  unfold occasion; rw [hk, hh]; exact sub_self _
end income
end YM.AllOrder.High
