import YM.LocalLTE.Motion.Queen
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open PhysicalNext.Repeat Roost
open YM.LocalLTE FrameBox Inset PriceCompiler
open LocalLTE.Fan Field Fan.Bakers Vine
variable {κ :ℝ}
-- on actual same epoch. Cane fixed R=base. δ tune.Numeral input scope.`Works` inside any H.
variable (f':ℕ→ℕ) (Q:H.fragrances) (hQ:East.lectures H j n f' Q) {I:Type} {φ : Filter I} (A:I→Rep G f) (G':∀ i,Cash W s a L X o U T (A i))
    (hS:Stamp T) (hw:Peers L s K X W o k j m n κ)
    (hc:∀ i,let H:=A i; H.path=R.path ∧ H.p=R.p∧ H.activities.reg=R.activities.reg ∧ H.activities.forced=R.activities.forced)
    (hE:∀ i:ℕ, f' i≤j→∀ V:Config G f, flags R.p.threshold V=∅ → Tendsto (fun x =>(A x).activities.E i V) φ (𝓝 (R.activities.E i V)) )
    (hA:Tendsto (fun x=> (A x).beta) φ (𝓝 R.beta))
local notation "ζ"=> (Inset.cone (-(1/2)) (betaF G s L))
local notation "Y"=> Fan.postponement L s o
-- convergence requires Packed pin and occupancy all x.Interpolation lemmas separately
variable (hK:∀ i, Coup.License j (A i) κ (betaF G s L) f' (L.val* Pressure.radiusB s))
open Bakers
-- keep D fixed, Stream.Seam. `runeOrbit` deterministic facing.Assets.Transfer.
variable (χ : Chi)
open Tensor
-- RP casting ALL f.E; no m at terminals. 
local notation "P'"=> (East.docket H Q)
local notation "K'"=> Option (Fin Q.fst)
local notation "C₀"=> Directions G c
local notation "G₀"=> Disk G c
section lift
variable (m)
def flying (R' : Rep G f) (i:ℕ)(L:Directions G c→L[ℝ] Directions G c) (x:Directions G c):= Field.speedΛ H Q.2 * (LocalLTE.stem (pie i+1) (East.maypole m H f' Q χ i R') (gStep R'.beta,L x))

def reins (R':Rep G f)(i:ℕ)(M:Directions G c→L[ℝ] Directions G c): Cabana.Pkt (Directions G c) (pie i+1):= fun j=> coeff (East.flying m H f' Q χ R' i M) j.val 0
lemma leases (i:ℕ)(A:Directions G c→L[ℝ] Directions G c) : East.reins m H f' Q χ R i A = Field.owner H (East.docket H Q) Q.2 i m f' A χ :=rfl
end lift
-- Comp of polynomial parameter and f yields continuous latest derivative.P-axis
section smooth
universe u
variable {E F A:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup A][NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ A]
lemma compose2 [FiniteDimensional ℝ E][FiniteDimensional ℝ F][FiniteDimensional ℝ A](f:E×F→A)(i:ℕ)(hh:ContDiff ℝ i f) : Continuous fun x:E=> coeff (fun y : F=> f (x,y)) i 0:= by
    let L : F→L[ℝ] E× F:=ContinuousLinearMap.inr ℝ E F
    let T: Tensor.T (E×F) A i→ₗ[ℝ] Tensor.T F A i:= {
       toFun k:=k.compContinuousLinearMap fun _=>L
       map_add' :=by intros; rfl
       map_smul' :=by intros; rfl }
    have hk:Continuous T:= T.continuous_of_finiteDimensional
    have he:∀ x:E, coeff (fun y:F=>f (x,y)) i 0 = (↑(Nat.factorial i):ℝ)⁻¹ • T (iteratedFDeriv ℝ i f (x,0)):= by
       intro x; let g(t:E×F):= f (t+(x,0)); have ht:F:=0
       rw [show (fun y:F=>f (x,y))=g ∘ L from funext fun v=> by change f (x,v)=g _; apply congr_arg; simp only [L,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero], Tensor.coeff, L.iteratedFDeriv_comp_right (show ContDiff ℝ i g from hh.comp (contDiff_id.add contDiff_const)) _ le_rfl,map_zero]; unfold g; rw [iteratedFDeriv_comp_add_right, zero_add]; rfl
    simp_rw [he]; have ht:Continuous (fun x:E=> T (iteratedFDeriv ℝ i f (x,(0:F)))):= hk.comp ((hh.continuous_iteratedFDeriv le_rfl).comp (show Continuous (fun x:E=>(x,(0:F))) by fun_prop)); exact ht.const_smul ((↑(Nat.factorial i):ℝ)⁻¹)
lemma changing {L:Type} [NormedAddCommGroup L][NormedSpace ℝ L]  [FiniteDimensional ℝ E] (i a:ℕ) [FiniteDimensional ℝ F] (K:L→ Tensor.T E F i)(v:L→E)(hp:ContDiff ℝ a K)(hv:ContDiff ℝ a v) : ContDiff ℝ a (fun x=> Tensor.diagonal (K x) (v x)):= by
    induction i generalizing F with
    | zero=> simp_rw [show ∀x, Tensor.diagonal (K x) (v x)= K x 0 from fun x=>congr_arg (K x) (Subsingleton.elim ..)]; exact ContinuousLinearMap.contDiff _ |>.comp hp (g:=(ContinuousMultilinearMap.apply ℝ _ _ 0)) -- edit
    | succ i ih=>
       let T:= continuousMultilinearCurryRightEquiv ℝ (fun _:Fin (i+1)=>E) F
       let t : Tensor.T E F (i+1)→ₗ[ℝ] Tensor.T E (E →L[ℝ] F) i:= {
          toFun f:= f.curryRight
          map_add' :=by intros; rfl
          map_smul':=by intros; rfl } -- edit multiline
       have he: ContDiff ℝ a (fun x=> Tensor.diagonal ((K x).curryRight) (v x)):= ih _ (t.toContinuousLinearMap.contDiff.comp hp)
       have h x: Tensor.diagonal (K x) (v x)= Tensor.diagonal ((K x).curryRight) (v x) (v x):=by unfold Tensor.diagonal; rw [ContinuousMultilinearMap.curryRight_apply]; congr 1; ext j; induction j using Fin.lastCases <;> simp
       simp_rw [h]; exact he.clm_apply hv

end smooth
section movement
variable [φ.IsCountablyGenerated]
variable (hκ:Coup.License j R κ (betaF G s L) f' (L.val*Pressure.radiusB s))
include hw hK hκ hA hE hS hQ hc G'
lemma shines (i:ℕ)(he:pie i+1≤k)(D:Directions G c→L[ℝ] Directions G c): Tendsto (fun z=> East.reins m H f' Q χ (A z) i D) φ (𝓝 (Field.owner H (East.docket H Q) Q.2 i m f' D χ)):=by
   let P(x:Rep G f)(j: Fin (pie i+1)):=Tensor.coeff (East.maypole m H f' Q χ i x) j.val 0
   have hp:Tendsto (fun x=> P (A x)) φ (𝓝 (P R)) := tendsto_pi_nhds.mpr fun j=> East.ornament H f' Q hQ A G' hS hw hc hE hA hK χ hκ i j.val (Nat.lt_of_lt_of_le j.isLt he)
   let b':=Cabana.Pkt (Disk G c) (pie i+1); let wF:(b'×ℝ)× Directions G c→ℝ:= fun x=> speedΛ H Q.2 * Cabana.actual x.1.1 (x.1.2,D x.2)
   have hs (x:Rep G f): (fun y=> wF ((P x,gStep x.beta),y))=East.flying m H f' Q χ x i D:=funext fun y=> congr_arg (fun f:(G₀)→ℝ=> speedΛ H Q.2*f (gStep x.beta,D y)) (show Cabana.actual (P x)=LocalLTE.stem (pie i+1) (East.maypole m H f' Q χ i x) from Fin.sum_univ_eq_sum_range (fun j:ℕ=> Tensor.diagonal (coeff _ j 0)) _) -- name
   have hQ:= H.laws.intake.positive
   apply tendsto_pi_nhds.mpr; intro j
   have hG := ((continuousAt_id.sqrt).inv₀ (Real.sqrt_pos.mpr hQ|>.ne') : ContinuousAt (fun x:ℝ=>gStep x) R.beta)
   have ht := (compose2 wF j.val ?_).continuousAt.tendsto.comp (hp.prodMk_nhds (hG.tendsto.comp hA))
   rotate_left
   · unfold wF Cabana.actual; simp_rw [Finset.sum_apply]; apply contDiff_const.mul; apply ContDiff.sum; intro d hd; refine East.changing d.val j (fun x:(b'×ℝ)×Directions G c=> x.1.1 d) (fun x=>(x.1.2,D x.2)) (?_) (by fun_prop)
     let e: b' →L[ℝ] Tensor.T (Disk G c) ℝ d:= ContinuousLinearMap.proj d; change ContDiff ℝ (↑(j:ℕ)) (e ∘ (Prod.fst ∘ Prod.fst)); exact (e.contDiff).comp (contDiff_fst.comp contDiff_fst)
   rw [← East.leases]; change Tendsto (fun z=> Tensor.coeff (East.flying m H f' Q χ (A z) i D) j 0) φ (𝓝 (Tensor.coeff (East.flying m H f' Q χ R i D) j 0)); simp_rw [← hs]; exact ht
end movement
end YM.PhysicalNext.Repeat.East
