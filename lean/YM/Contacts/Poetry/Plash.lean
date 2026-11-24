import YM.Contacts.Poetry.Pens
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
/-! adapting Marlin/Foam. Leave actual modelI separated. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} (B : BudgetPoint) (C : Listing G c) (z w : ℕ) {p d a δ q Y E : ℝ}
variable (T : Collection.Source G c) (g t:Trio.Offer G c) (V:Config G c)
local notation "P" => lodge C z w
local notation "U" => (bison T g t)
local notation "θ" => (C.read T)
lemma moverz (u:Seat c)(r:ℕ)(i:Site c) : neighbors r (Meadow.spin u i)=u.spread (neighbors r i):= by
  let v:= Meadow.spin u
  have hp (x): separation (v i) (v x)=separation i x:= by change separation (u.1.act i+u.2) (u.1.act x+u.2)=_; rw [separation_translate,separation_signed]
  ext x; obtain ⟨k,rfl⟩:=v.surjective x; change v k∈ neighbors r (v i) ↔ v k∈ (neighbors r i).image v; rw [neighbors_mem,hp k]; simp only [Finset.mem_image,neighbors_mem, Equiv.apply_eq_iff_eq]; grind

local notation "N" => pluck B (lodge C z w)
local notation "D" => poursP B (lodge C z w) U
-- apply for χ(T!). scalar V0
variable {R : Listing G c} (F : Collection.Source G c) (hf : ∀ i,R.hard i=C.hard i ∧ F.hardRead i=T.hardRead i) (W : PathData G) (b : Clip) (β τ φ x : ℝ)
   (hV : Ingredients (lodge C z w) (dummy (bison T g t)) (raiser B) 0 Y)
include hV hf
lemma elicits (M:Trio.Offer G c)(r:ℕ)(hM:Trio.Mirrors M) (h : Meadow.Budget B C.reg T.logRead E) (ht: ∀ V:Config G c,(R.read F).additive B V= (θ).additive B V+Fintype.card (Site c)*x + (∑ i, masked B.threshold (neighbors z i) (g i) V)+(∑ i:Site c,t i V) + ∑ i : Site c, masked B.threshold (neighbors r i) (M i) V)
    (hs:∀ s b, Nonempty ((R.read F).Moves s b)) (hp:∀ s b,Nonempty ((C.read T).Moves s b)) : earlyValue R W b B F β τ φ V=earlyValue (N) W b B (D) β (τ-x) φ V * Real.exp (-∑ i:Site c,masked B.threshold (neighbors r i) (M i) V):= by
  let X := (P); let y:=leanU c; let f i:= masked B.threshold (sea z i).support (choir (g) i) V; let t' (i: Door c):=choir (-t) i V
  have he : (((N).read D).additive B V)=(θ).additive B V +∑ i,f i:= by
    let g'(i: Civ c):= Sum.elim (fun i=>(θ).regularOccurrence B i V) f i
    have hh : ∀ i:Civ c, ((N).read D).regularOccurrence B (y.symm i) V=g' i:= by intro i; change masked _ (Sum.elim C.reg (sea z) (y (y.symm i))|>.support) (Sum.elim _ _ (y _)) _= _; rw [Equiv.apply_symm_apply]; cases i<;> rfl
    have hu : (N|>.read D).additive B V=∑' i,g' i := by
      rw [← y.tsum_eq g']; unfold Activities.additive; refine tsum_congr fun i=>?_ ; rw [← hh,Equiv.symm_apply_apply]
    rw [hu]; exact Summable.tsum_sum (f:=g') (stashes B C T V h) Summable.of_finite|>.trans (congr_arg ((θ).additive B V + ·) (tsum_fintype f))
  have hg : ∑' i,(U).logarithm i V= ∑ i,t' i:= by
    let f' : Civ c→ℝ:= Sum.elim 0 t'
    have hp : ∑' i,(U).logarithm i V=∑' i, f' (y i):= by refine tsum_congr (fun i=>?_); change Sum.elim (fun _:ℕ=> (0:Config G c→ℝ)) (choir (-t)) (y i) V=_; cases y i <;> rfl
    rw [hp,y.tsum_eq f', Summable.tsum_sum (f:=f') (show Summable (fun i : ℕ=> f' (.inl i)) from summable_zero) Summable.of_finite]; simp [f']
  let c':=(Fintype.card (Site c):ℝ)
  let Mζ V:=∑ i:Site c,masked B.threshold (neighbors r i) (M i) V
  have hA:(R.read F).additive B V - (θ).additive B V- c'*x-Mζ V=(∑ i,f i)- ∑ i,t' i:= by
    let gb (_u:Seat c):= (R.read F).additive B V - (θ).additive B V-c'*x-Mζ V
    have h(u: Seat c): (∑ i:Site c,f (u,i)) - ∑ i:Site c,t' (u,i)=Rim c*gb u := by
      have hb: (R.read F).additive B (u.view V)= (R.read F).additive B V:= streams B V F 0 u.1 u.2 _ (hs _ _|>.some)
      have hp: (θ).additive B (u.view V)= (θ).additive B V:= streams B V T 0 u.1 u.2 _ (hp _ _|>.some)
      have hz : Mζ (u.view V)=Mζ V:= by
        unfold Mζ
        conv_rhs => rw [← Equiv.sum_comp (Meadow.spin u) (fun i=> masked B.threshold (neighbors r i) (M i) V)]
        apply Finset.sum_congr rfl; intro i _
        let x:=u.spread (neighbors r i); have he: neighbors r (Meadow.spin u i)=x:= moverz u r i
        rw [he,show M (Meadow.spin u i)= M i ∘ u.view from (funext fun V=> (hM i u.1 u.2 V).symm),u.distribute]
        rfl
      have ht:= ht (u.view V); rw [hb,hp] at ht
      have hv i:t' (u,i)=Rim c * (-(t i (u.view V))):=rfl
      have hF i:f (u,i)=_:= tune (leap z) g u i V B -- Offer binder issue
      simp_rw [hF,hv, ← mul_sum,Finset.sum_neg_distrib]; unfold gb; rw [ht]; change _-_ = _ * (_+c'*x+_+_+ Mζ (u.view V)-_- _ - Mζ V); rw [hz]; ring -- edit
    rw [Fintype.sum_prod_type (f:=f), Fintype.sum_prod_type (f:=t'),← sum_sub_distrib]; simp_rw [h]; unfold gb; rw [sum_const,card_univ,nsmul_eq_mul, ← mul_assoc,Song.balance,one_mul]
  have hG : (P|>.pours U).gas B V=(R.read F).gas B V := by
    have hQ i:(P|>.pours U).admissible B V i↔ (R.read F).admissible B V i:= by unfold Activities.admissible; rw [show ((P).pours U).forced=(R.read F).forced from funext fun i=> (hf i).1.symm]
    unfold Activities.gas; refine tsum_congr (fun i=>?_); unfold Activities.gasOccurrence; rw [propext (hQ i)]; split; next=> exact prod_congr rfl fun i hi=> (congr_fun (hf i).2 V).symm
    exact rfl
  have hx: (N|>.read D).gas B V=(R.read F).gas B V*Real.exp (∑ i,t' i):= by rw [pulpy_T hV, hg, hG]
  unfold earlyValue Rep.eval Rep.exponent Collection.frozen; dsimp only; rw [he,hx]; change _ = (_* (_ * Real.exp _)* _)*Real.exp (-Mζ V)
  have hv: ∀ a b c d:ℝ,a*(b*c)*d=a*c*d*b:=fun a b c d=> by ring
  rw [hv, mul_right_comm _ ((R.read F).gas B V) (Real.exp _)] -- ambiguity
  rw [mul_right_comm _ ((R.read F).gas B V) (Real.exp _)]
  apply congr_arg (· * ((R.read F).gas B V)); rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; apply congr_arg Real.exp; linarith
end YM.PhysicalNext.Repeat.Marlin
