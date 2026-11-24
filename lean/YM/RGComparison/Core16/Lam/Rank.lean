import YM.RGComparison.Core16.Lam.Wrap
import YM.RGComparison.Core16.Lam.Sun
/-!
# Spar Ω_Θ on the unmasked V/g scheme (top seam); no eta remainder at THIS Hess stencil estimator.
Budget of old roll stays charged even when shifting. Keep valuation & logarithm condition in PowerSeries,
no convergence assertion. Product before expectation. Growth of outputs passes also period dominance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {P: Patch} {K:KernelChoices} {d:f.val=c.val*P.L.val} {I:Type}
    (W:Oven P)(X:Shelf G (PlaqAxes⊕Axis) W.Xways)

section parts
variable {p:Patch}
omit W X in
lemma hush {C : ℕ} {n:ℕ} {V:ℕ→Roll}(hv: ∀ i < C, V i=0)(hx:n<C): nth n (day V 0)=0:=by
    unfold nth day dawn; rw [PowerSeries.coeff_mk,nth,map_sum]; apply sum_eq_zero; intro i h
    rw [hv i (by simp only [mem_range] at h; omega),shiftFront,mul_zero,map_zero]

variable {X} {A B k T L:Type}[Fintype k][Fintype L][Fintype T][Fintype I][Fintype B][Fintype A]
    {p' : Finset I}{u : News G c}
private lemma shade {U:Planet X f I k T}{p:Stuff G I L}{ψ:(L→ G.Color)→ℝ} (Y:U.Steady) (_hψ: ContDiffAt ℝ ω ψ 0) {n} (he:Zeros n ψ) (i:ℕ)(hi:i<n): nth i (stamps U p ψ)=0:=by
    apply hush (C:=n) _ hi; intro j hj
    have hz:=he j hj; have ht:tale p ψ j=0:= by funext x u; unfold tale; rw [hz]; rfl
    apply train.unique (solder U _ _ Y [] j); have he: train (0:Cost) 0:=by simpa only [map_zero] using! train.cash 0
    refine he.travel (Fk.tollLess ?_); filter_upwards [willing Y.prices] with i hi; rw [ht,sight, show sing (G:=G) (ι:=I) [] (_) =1 from rfl,one_mul]; exact (burden Y hi 0).symm -- pp f
end parts
local notation "S"=> StepData.mk P K d

variable (B:Forest (StepData.mk P K d).ratio)
local notation "U"=> gear S B X
-- stencil shorthand; make Fk cost forecast independent and `K.structures` as Ops

def bud (i : Operand G c): Roll := stamps U (harp B X i) (tileΨ W K (profileDatum i))
def smooth (i j:Operand G c): Roll := stamps U (harp B X i) (heatΨ W K (tier i j))
def osier (i j:Operand G c):Roll:= joining U (harp B X i) (harp B X j) (tileΨ W K (profileDatum i)) (tileΨ W K (profileDatum j))
def pokes (i j:Operand G c):Roll:= smooth W X B i j-pursed.solder 2 (osier W X B i j)

def polls (R:StepData c f)(i j:Operand G c) (g:ℝ):= Lam.measure R g (compass i) (compass j)

variable {W X}
variable (hS:P.Branches K G) (hW: Parcel.Oven.Offers W X K) (H: Bid.Larger (G:=G) (StepData.mk P K d))
include hS
lemma daily (W:Oven P) (j:Axis ×G.ColorIndex): ContDiffAt ℝ ω (tileΨ W K j) 0∧Zeros 1 (tileΨ W K j):= by
    obtain ⟨ht,hv,-⟩:= public_plate W hS (colors G j.2) (colors G j.2) j.1
    exact ⟨ht,fun i hi=> Tested.jets_vanish (ht.of_le le_top) (zero_first (ht.of_le le_top) hv) hi⟩
lemma hourly (W: Oven P) (j:(Axis × G.ColorIndex) × Axis × G.ColorIndex): ContDiffAt ℝ ω (hearth W K j) 0 ∧ Zeros 2 (hearth W K j):= by
    obtain ⟨ha,hb⟩:= daily hS W j.1; obtain ⟨ht,hk⟩:=daily hS W j.2
    let F:= hearth W K j; have h :ContDiffAt ℝ ω F 0:= Silk.mixed_hot ha ht
    have hA (x:W.Xways⊕W.Xways → G.Color) : Bill 2 (fun t:ℝ=> F (t • x)):=by
        let u : W.Xways→ G.Color:= x ∘ Sum.inl; let v:= x ∘ Sum.inr
        exact bill_mul (Descent.bill_of_grade (directions (ha.of_le le_top) u) (fun i hi=> congr_fun (hb _ hi) u)) (Descent.bill_of_grade (directions (ht.of_le le_top) v) (fun i hi=>congr_fun (hk _ hi) v))
    exact ⟨h, fun i hi=> Tested.jets_vanish (h.of_le le_top) hA hi⟩
lemma yearly (W: Oven P)(i:Bool× Axis × G.ColorIndex × G.ColorIndex) : ContDiffAt ℝ ω (heatΨ W K i) 0:=by
    unfold heatΨ; split; exact (public_plate W hS ..).2.2; exact contDiffAt_const
omit hS
include H hW
-- abstract Viewer congruence
lemma presents (ψ:(I→ G.Color)→ℝ) [Fintype I] {p: Stuff G B.Free I} {k:News G c→ℝ}{n C}(hv:Visible X ψ (scoop S B k) p n C)(hx: ContDiffAt ℝ ω ψ 0)(h:ContDiff ℝ ∞ k):
    train (fun g=>port S B g k) (stamps U p ψ):=by
    apply (Silk.booked (U) (paint S B hW H) hv (hx.of_le le_top)).travel
    filter_upwards [Fk.tollLess (willing hW.good)] with x hx; exact (turned_bill S B hW H h hx).2.symm
lemma valenced (i j:Operand G c) (u:ℕ)(hu:u<2): nth u (osier W X B i j)=0 := by
    let I:= U; let a:=profileDatum i; let b:=profileDatum j; let A:= daily H.1 W a; let B':= daily H.1 W b; let h := paint S B hW H; let T:= hourly H.1 W (a,b)
    have he k (hk:k<1): nth k (bud W X B i)=0 := shade (P:=P) W h A.1 A.2 k hk -- name clash
    have hz k (hk:k<1): nth k (bud W X B j)=0 := shade W h B'.1 B'.2 k hk
    change PowerSeries.coeff u (_-bud W X B i*bud W X B j)=0
    rw [map_sub,PowerSeries.coeff_mul,Finset.sum_eq_zero,sub_zero]; swap
    · intro j' hJ; have ht:= mem_antidiagonal.mp hJ; exact mul_eq_zero.mpr (by by_cases h:j'.1<1; exact Or.inl (he _ h); exact Or.inr (hz _ (by omega)))
    exact shade W h T.1 T.2 u hu

lemma supplies (i j:Operand G c): train (polls S i j) (pokes W X B i j):=by
    obtain ⟨C,hc⟩:= seals G K; let p:=raise S (compass i); let q:= raise S (compass j)
    let u (f:News G c→ℝ) g:= port S B g f; let F:= u (tip S (compass i) (compass j)); let V:=u (p*q)-u p* u q
    have ht:train F (smooth W X B i j):= Lam.presents _ hW H _ (hued hW B H hc i j) (yearly H.1 W (tier i j)) (tip_hot ..)
    have hp(v:Operand G _):train (u (raise S (compass v))) (bud W X B v):= Lam.presents _ hW H _ (visor hW B H hc v) (daily H.1 W (profileDatum v)).1 (raise_hot ..)
    have he: train V (osier W X B i j):= (Lam.presents _ hW H _ (fusion hW B H hc i j) (hourly H.1 W (profileDatum i,profileDatum j)).1 ((raise_hot S _).mul (raise_hot S _))).deduct ((hp i).produces (hp j))
    have hh: train (fun g=>g⁻¹^2 * V g) (pursed.solder 2 (osier W X B i j)):= train.sand (Aspiration.shift he (valenced B hW H i j))
    refine (ht.deduct hh).travel (Tested.eventually_pos.mono fun x hx=>?_); unfold polls; rw [measure_point S B H.1 hx.ne']; unfold V F u; simp only [Pi.sub_apply,Pi.mul_apply,inv_pow,div_eq_inv_mul]; rfl -- arithmetic inv_neg
lemma convention (i j:Operand G c) {W': Oven P}{X': Shelf G (PlaqAxes ⊕ Axis) W'.Xways} (B':Forest (StepData.mk P K d).ratio) (ht : W'.Offers X' K):
    pokes W X B i j=pokes W' X' B' i j := (Lam.supplies B hW H i j).unique (Lam.supplies B' ht H i j)
end YM.RGComparison.Core16.Lam
