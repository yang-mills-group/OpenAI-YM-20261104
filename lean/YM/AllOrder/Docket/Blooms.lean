import YM.AllOrder.Docket.Tier
import YM.AllOrder.Catch.Span
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Aux
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PertExtension.Series Laplace Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open Catch Catch.Clock Sienna 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
namespace Name
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
variable (A: Aux.Name G P K u x r (k+3) U)
local notation "I"=>Aux.Name G P K u x r (k+3) U
local notation "ξ"=> Aux.scope x
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
open Till Tilt Lantern
local notation "F"=> A.Fs
local notation "X"=> A.X
local notation "Y"=> Body A.Vx
variable {O:ChartRatio G}(hO:LocalRatio O)
variable (W:ι→Aux.Name G P K u x r (k+3) U) (h:Proper W T)
set_option quotPrecheck false
local notation "V'"=>fun i=> (W i|>.Bank O)
local notation "b'"=> (fun i=> (W i).Θ)
local notation "hX"=> T.Meter
set_option quotPrecheck false
local notation "Λ"=> T.rail
local notation "R"=> fun i=> (W i).Qc
local notation "K'"=> fun i=> (W i).Ph
local notation "M₁"=> fun i=> (W i).Mh
local notation "Q'"=> fun i=> (W i).Zc
variable (D) (hD:0<D) {p:ι→ℝ}
local notation "Z"=> fun i=> (W i).aster O hO
local notation "Z'"=> fun i=> (W i).call O hO
variable (l:ℕ)
open Fire
include h
section probe
omit h in
lemma aux_burden {V:ι→Type}[∀ i,NormedAddCommGroup (V i)]{u:∀i,V i} {b:ι→ℝ}(hp:hX (fun i=> ‖u i‖) a) (he:T.Meter b a)
 : (T.book (fun i=> Metric.closedBall (u i) (b i))).Meter (fun i=> ‖i.2.1‖) a := by
 let L i:= {y:V i//y∈ Metric.closedBall (u i) (b i)}; let v:Sigma L→ι:=Sigma.fst; let hρ:= T.liftF v; apply ((hp.add he).pays v hρ).smaller;
 filter_upwards with i; let f:= (i.2:V i.1); have hh: ‖f-u i.1‖≤ b i.1:= mem_closedBall_iff_norm.mp i.2.2; rw [abs_of_nonneg (norm_nonneg _)]; let S:V i.1:=u i.1; refine le_trans (b:=‖S‖+b i.1) ?_ (le_abs_self _); change ‖f‖≤ ‖S‖+_; rw [show f=(f-S)+S from (by abel)]; exact (norm_add_le ..).trans ((add_le_add hh le_rfl).trans_eq (add_comm ..))
omit h in
lemma pol_b (v:X): Fire.Rank (A.X) (j+2) (A.aster O hO j):= (Fire.radius (A.tall O hO) j).sub (Fire.Rank.nil (j+2) (A.intercept O j))
variable {y z:∀i,(W i).X}
include hD
lemma awake (hy:hX (fun i=> ‖y i‖) (-(1/2:ℝ)))(hg:∀ᶠ i in Λ,(W i).goods O D (p i) (z i))(hp:hX p 0)(b:ι→ℝ)(ht:hX b (-(1/2:ℝ)))(h':∀ᶠ i in Λ,0<b i) (hj:j≤k): Catch.Cover T l 0 (fun i=> (b i)⁻¹) (fun i x=> Z i j ((W i).tulip x)) y:= by
 let L:= T.bookF (fun i=>Metric.closedBall (y i) (b i)); let hf := Proper.sail W h _ _ L; have hG:= L.tends.eventually hg; apply (Warp.action (Q:=T) (V:=fun i=> (W i).X) (n:=j+2) l ?_ ?_ h');
 · apply Eventually.of_forall; intro i; let u:= (W i|>.Θ)⁻¹ • ContinuousLinearMap.id ℝ ((W i).X); exact (pol_b (W i) hO (0:(W i).X)).lead u -- syntax
 exact ((local_ticket D hO _ hf hD (z:=fun i=> z i.1) hG (Name.aux_burden hy ht) (hp.pays _ L)).2.steps j hj) -- y parameter not infer
abbrev grain (O:ChartRatio G)(hO:LocalRatio O)(q:ℕ) (u:A.X):= A.Θ^q • A.aster O hO q (A.tulip u)
-- trunc out upper order q rank.Inverse uses teacher for diff.
local notation "δ"=> (fun i=>W i|>.Θ)
lemma windy (hy:hX (fun i=> ‖y i‖) (-(1/2:ℝ)))(hg:∀ᶠ i in Λ,(W i).goods O D (p i) (z i))(hp:hX p 0)(b:ι→ℝ)(ht:T.Meter b (-(1/2:ℝ)))(h':∀ᶠ i in Λ,0<b i) (hj:j≤k):
    Catch.Cover T l (graded j) (fun i=>(b i)⁻¹) (fun i=> grain (W i) O hO j) y:= by
   -- multiply any cover with time, Move.SR.
   let X':=δ; let g i:= X' i^j; let f i x:=(W i|>.aster O hO j ((W i).tulip x)); intro e hc; let hV:= awake D hO W h hD l hy hg hp b ht h' hj; have hx:T.Meter g (graded j):=(Proper.meter W h).1.pow j; let s:=(e-graded j)/2; have hs:0<s:=div_pos (sub_pos.mpr hc) (by norm_num); filter_upwards [T.positive,hx (s+graded j) (by linarith), hV s hs] with i hi hv hp; exact (hp.smul (X' i ^ j)).climb (by refine (mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hi.le _)).trans_eq ?_;rw [← Real.rpow_add hi,show s+graded j+s=e by unfold s; ring]) le_rfl
lemma wise {hj:j≤k}(hy:hX (fun i=> ‖y i‖) (-(1/2:ℝ)))(hg:∀ᶠ i in Λ,(W i).goods O D (p i) (z i))(hp:hX p 0)(b:ι→ℝ)(ht:T.Meter b (-(1/2:ℝ)))(h':∀ᶠ i in Λ,0<b i) : Catch.Cover T l 0 (fun i=>(b i)⁻¹) (fun i=> (W i|>.call O hO j)) y:= by
   let A i t:= grain (W i) O hO t; let Q:= range (j+1); let S' := fun u:Finset ℕ=> (fun i=>(∑ j∈u, A i j)); have he u (hu:u⊆Q) : Catch.Cover T l 0 (fun i=>(b i)⁻¹) (S' u) y:= by
     induction u using Finset.induction_on with
     | empty=> unfold S'; simp only [sum_empty]; exact Cover.fixed (fun i=> (0:ℝ)) (h'.mono fun _ hi=> inv_nonneg.mpr hi.le) (by simp only [norm_zero]; exact Meter.const _ _ ) -- parameters ambiguity
     | insert i u hv ih=> unfold S'; simp only [sum_insert hv]; refine Cover.add ((windy D hO W h hD l hy hg hp b ht h' (by have h:=mem_range.mp (hu (mem_insert_self ..)); omega)).weak ?_) (ih (fun j hj=>hu (mem_insert_of_mem hj))); unfold graded; linarith [Nat.cast_nonneg (α:=ℝ) i]
   rw [show (fun i=> W i |>.call O hO j)= S' Q from funext fun i=>funext fun v=>(Finset.sum_apply v Q (A i)).symm]; exact he Q (subset_refl _)
lemma omegaL (hj:j≤k)(hy:hX (fun i=> ‖y i‖) (-(1/2:ℝ)))(hg:∀ᶠ i in Λ,(W i).goods O D (p i) (z i))(hp:hX p 0)(b:ι→ℝ)(ht:T.Meter b (-(1/2:ℝ)))(h':∀ᶠ i in Λ,0<b i): Catch.Cover T l (graded (j+1)) (fun i=>(b i)⁻¹) (fun i=> ((W i|>.call O hO k)-(W i|>.call O hO j))) y:= by
   let f u i:=(W i|>.call O hO u); let z:= (fun i=> (b i)⁻¹); have hx i a:(f (i+1) a)= (f i a) + grain (W a) O hO (i+1):= funext fun v=> Finset.sum_range_succ .. -- + binder
   suffices he:∀ u,j ≤ u→u ≤ k→ Catch.Cover T l (graded (j+1)) z (fun i=> (f u i)-(f j i)) y from he k hj le_rfl
   intro v he ht'; induction he with
   | refl=> simp_rw [sub_self]; exact Cover.fixed (fun i=> (0:ℝ)) (h'.mono fun _ hi=>inv_nonneg.mpr hi.le) (by simp only [norm_zero]; exact Meter.nil _ _) -- `_`
   | @step v hv ih=> simp_rw [hx,add_sub_right_comm]; exact Cover.add (ih (by omega)) ((windy D hO W h hD l hy hg hp b ht h' ht').weak (by unfold graded; push_cast; linarith [Nat.cast_le (α:=ℝ)|>.mpr hv]))
end probe
end Name
end YM.AllOrder.Aux
