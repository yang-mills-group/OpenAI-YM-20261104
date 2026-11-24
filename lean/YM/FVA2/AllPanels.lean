import YM.FVA2.FirstPanel
import YM.FormalOPE.RG10.Sync.Kernels

/-!
# Exact later-stage transfer implemented by Fk reads and Route steps

Can use genuine analytic parts in `Fk.read` and only a per-order finite
remainder of the input ticket. `receipt` / extra bill recovered as a
polynomial on the *full* open fields, conditional denom `Update.W` kept.
Records the efficient special case where the step's ray includes the current
true Hessian and the given Penalty, so that we feed the exact W on that shell.
No limits, uniform widths or relation to the infinite-volume real law assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bk
open Filter Topology Function Finset MeasureTheory
open FormalOPE.RG10 FormalOPE.RG10.MarkovChain OpenSlots
open RGComparison.Core16 RGComparison.Core16.Lumen Lumen.Planet
open PertExtension Precision Inherit Push.Loops PertExtension.Chart Lattice RG
    PertExtension.GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
    Papers Warp Line Roof Router Quadratic
open scoped Classical Topology ContDiff BigOperators InnerProductSpace
variable {G:Gauge} [Nontrivial G.Color] {I A B E : Type} [Fintype I]
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {p:Permit E}

-- coefficients as finite list of homogeneous polynomials. Revenue only invoiced once.
structure Solid (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] where
    p : Permit E
    order : ℕ
    sale : ∀ a:ℝ, ∀ x:E,p.val (a • x)= a ^ order * (p.val x)
namespace Solid
variable (M N: Solid E)
def combine : Solid E where
   p := M.p*N.p
   order:=M.order+N.order
   sale a x:= by change M.p.val _ * N.p.val _=_*(M.p.val _ * N.p.val _); rw [sale,sale,pow_add]; ring

def carrying (M:List (Solid E)) : Permit E:= (M.map Solid.p).sum
variable (u v:List (Solid E))
lemma grows : carrying (M :: u)= M.p + carrying u:= rfl
lemma becomes : carrying (u++v)=carrying u + carrying v:= by simp [carrying]
lemma product_left : carrying (v.map M.combine)=M.p*carrying v:= by induction v with
                                            | nil=> unfold carrying; simp
                                            | cons a v ih=> rw [List.map_cons,grows,grows,ih,mul_add]; rfl
lemma product_both : carrying (u.flatMap fun x=> v.map x.combine)=carrying u * carrying v := by
   induction u with
   | nil=> unfold carrying; simp
   | cons h t ih=> rw [List.flatMap_cons,becomes,grows, ih,add_mul, product_left]
lemma support (p:Permit E) : ∃ u:List (Solid E), p=carrying u:= by
   suffices he:∃ u:List (Solid E),p.val=(carrying u).val by obtain ⟨u,hu⟩:=he; exact ⟨_,Subtype.ext hu⟩
   refine Papers.induction (P:=fun x:E→ℝ=>∃ u:List (Solid E),x=(carrying u).val) ?_ ?_ ?_ ?_ p.property
   · intro v; let z:Solid E:= ⟨⟨v,Papers.linear v⟩,1,fun a x=> by change v _ = _* v x; rw [map_smul,pow_one]; rfl⟩; exact ⟨[z],by simp [carrying,z]⟩
   · intro v; let z:Solid E:=⟨⟨_,Papers.fixed v⟩,0,fun a x=> by rw [pow_zero,one_mul]⟩; exact ⟨[z],by simp [carrying,z]⟩
   · rintro _ _ _ _ ⟨u,rfl⟩ ⟨v,rfl⟩; exact ⟨u++v, by rw [becomes]; rfl⟩
   rintro _ _ _ _ ⟨u,rfl⟩ ⟨v,rfl⟩; exact ⟨ _, show _=(carrying (u.flatMap fun x=> v.map x.combine)).val from by rw [product_both]; rfl⟩
def list (p:Permit E) := (support p).choose
lemma payload (p:Permit E) : carrying (list p)=p:= (support p).choose_spec.symm
lemma viable : ContDiffAt ℝ ω M.p.val 0:=
    Papers.induction (P:=fun x:E→ℝ=>ContDiffAt ℝ ω x 0) (fun v=> (LinearMap.toContinuousLinearMap v).contDiff.contDiffAt) (fun _=> contDiffAt_const) (fun _ _ _ _ hf hg=> hf.add hg) (fun _ _ _ _ hf hg=>hf.mul hg) M.p.property
lemma tolls : Stack.rise M.p.val= PowerSeries.X ^ M.order * PowerSeries.C M.p:= by
    apply Stack.into; intro x; have he:= directions (M.viable.of_le le_top) x
    simp_rw [M.sale] at he
    rw [mul_comm (X ^ M.order), ← monomial_eq_C_mul_X_pow] -- check
    apply PowerSeries.ext; intro i; rw [read_rise, reading_term, coeff_monomial];
    rw [show jet M.p.val i x = (if i=M.order then M.p.val x else 0) from congr_fun (he.unique (Aspiration.single _ _)) i]
    split <;> rfl
end Solid

section Fk_mean
variable (U:Quadratic ((Direction G I) × E))(S:Direction G I × E→ℝ)(t:ContDiffAt ℝ ω S 0)
    (hU:∀ a,U.flourish a=2*jet S 2 a)(h:(core U).RespectsPrice) (J: ChartRatio G) (HJ:LocalRatio J) (y:E)
local notation "W"=> rayBlock J S
local notation "μ"=> tangent G I
variable (f:Ticket (Direction G I × E))
lemma upt_pow (k:ℕ): uptake U μ h (X^k * f)= X^k * uptake U μ h f:= by
  apply PowerSeries.ext; intro i; unfold uptake throughPrice; simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk,coeff_X_pow_mul']; by_cases he:k ≤ i <;>simp [he]
lemma fitPow (Vw:Ticket (Direction G I × E)) (k:ℕ): fit U μ h (X^k * f) Vw=X^k * fit U μ h f Vw:= by
    rw [fit,mul_left_comm Vw, upt_pow, mul_assoc]; rfl
variable {f}

variable {X' T D : Type} [Fintype T][Fintype D]
variable {n:Side}{Ξ:Shelf G A D}{P:Planet Ξ n I T X'}(hP:Fk.rise P=ᶠ[𝓝 0] mount y S)
-- linearly extend `Fk.read` using external coupling power. No discarded negative ranks.
def orderUnit (y:E)(M: Solid (Direction G I × E)) (J:ChartRatio G)(P : Planet Ξ n I T X'):= PowerSeries.mk (Fk.read P J (origins G I) (stampF y M.p.val) M.order)
include hP t hU HJ
lemma valueUnit (M:Solid (Direction G I × E)) : orderUnit y M J P=Stack.read y (fit U μ h (PowerSeries.C M.p) W) := by
    unfold orderUnit; rw [OrdersAt y J HJ S t U hU h hP M.p.val M.viable _ _ (placed y M.p.val), M.tolls,fitPow,map_mul,map_pow,Stack.read,PowerSeries.map_X, Stack.drop_mul]

-- invoice all terms

def valueMany (y:E)(M:List (Solid (Direction G I × E)))(P:Planet Ξ n I T X')(J: ChartRatio G): PowerSeries ℝ:= (M.map fun a=> orderUnit y a J P).sum
omit t hU HJ hP
lemma fitSum (V Tw Z: Ticket (Direction G I × E)): fit U μ h (V+Tw) Z=fit U μ h V Z+fit U μ h Tw Z:= by unfold fit; rw [mul_add,map_add,add_mul]
include hP t hU HJ
lemma values (M:List (Solid (Direction G I × E))): valueMany y M P J= Stack.read y (fit U μ h (PowerSeries.C (Solid.carrying M)) W):= by
    induction M with
    | nil=> simp [valueMany,Solid.carrying,fit]
    | cons x l ih=> change orderUnit y x J P + valueMany y l P J=_; rw [Solid.grows,map_add, fitSum,map_add,valueUnit U S t hU h J HJ y hP, ih]

def priceEntries (y:E)(w:Ticket (Direction G I × E))(P:Planet Ξ n I T X')(J:ChartRatio G): PowerSeries ℝ := PowerSeries.mk fun i=> coeff i (∑ k ∈ Finset.range (i+1), PowerSeries.X^k * valueMany y (Solid.list (coeff k w)) P J )
lemma accrued (w:Ticket (Direction G I × E)): priceEntries y w P J= Stack.read y (fit U μ h w W):= by
   apply PowerSeries.ext; intro n; rw [priceEntries,coeff_mk]; let a:=fun k : ℕ=> PowerSeries.X^k * PowerSeries.C (coeff k w)
   have ht : Through n w (∑ k ∈ range (n+1), a k):= by intro i hi; unfold a; rw [map_sum]; simp_rw [mul_comm (X^_), ← monomial_eq_C_mul_X_pow,coeff_monomial]; simp [hi]
   have he : Through n (fit U μ h w W) (fit U μ h (∑ k ∈ range (n+1),a k) W):= Through.mul (keepsThrough _ ((Through.refl _).mul ht)) (Through.refl _)
   have h₁(s:Finset ℕ) : fit U μ h (∑ k∈s,a k) W=∑ k∈s,fit U μ h (a k) W:= by unfold fit; simp [Finset.mul_sum,Finset.sum_mul]
   rw [reading_term,he n le_rfl,← reading_term,h₁,map_sum (Stack.read y)]; congr 1
   refine Finset.sum_congr rfl (fun i _=>?_)
   rw [values U S t hU h J HJ y hP, Solid.payload,show a i= _ from (rfl:a i=X^i * PowerSeries.C (coeff i w)), fitPow, map_mul,map_pow,show Stack.read y X=PowerSeries.X from PowerSeries.map_X _]

-- `priceEntries` uses read with its own analytic weights. Supply all interactions
-- left over (not just marks), via polynomial tickets. Full open denominator read.
def extras (w: Ticket (Direction G I × E)) : Ticket (Direction G I × E):= Return W*w
lemma change_body (w:Ticket (Direction G I × E)) : Stack.read y (uptake U μ h w) = Stack.read y (uptake U μ h W) * priceEntries y (extras S J w) P J := by
    rw [accrued U S t hU h J HJ y hP,← map_mul, fit_eq _ _ _ _ _ (rayStart J HJ S), extras, ←mul_assoc, spend_it (rayStart J HJ S),one_mul]
end Fk_mean
end YM.FVA2.Bk
