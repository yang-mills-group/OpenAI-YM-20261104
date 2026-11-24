import YM.LocalLTE.Tol.Album
import YM.LocalLTE.Georges.Field
/-!
# Real calibrated cylinder supplies. Hold section stencils including cover placement. All LABEL directions in calibrated canonical finite requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port.Sect
open Filter Function Set Lattice Wilson Labels Overlay Marker Source RG Finset Pressure MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Animals FrameBox Grove Cabana
open Work.H03 Next.Foundations ConnectedActivityE6 Blaze Brush
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{d k:ℕ}
set_option quotPrecheck false
-- before schedule choose b
variable (G) (D0:ℕ)
lemma garden : ∃ b,∀ (k:ℕ),k ≤ D0→∀ (n:Side)(x:Site n), (localSection G k).footprint x⊆ neighbors b x:=by
    choose b h using fun i : Fin (D0+1)=> Sect.insideL G i.val
    refine ⟨Finset.univ.sup b,fun i hi n x y hy=>?_⟩
    let v: Fin (D0+1):= ⟨i,Nat.lt_succ_of_le hi⟩; exact (neighbors_mem ..).2 (((neighbors_mem ..).1 (h v n x hy)).trans (Finset.le_sup (Finset.mem_univ v)))
-- unified pricing.Beta permit.GF.Arch. fee can grow BEFORE J.P ; select as function of params, not stamps.
open Extra.Histories RG.Supply Supply
open LoopBank
variable (b M CB:ℕ)(μ ζ κ:ℝ) (i:ℕ) {v:ℝ}(hμ:0≤μ)(he:0<ζ)(hv:ζ<(i:ℝ)/4)(hκ:Reliable G κ v)
variable (P:Stage)
local notation "F" i=> (Labels.frames G).level i
private abbrev tune (G:Gauge)(d₁ p k:ℕ):= max (Multi.Maquette.upper (localSection G d₁)) (Next.Foundations.price G (d₁+p+k))
def payT (G:Gauge)(D p j:ℕ):ℝ:= (∑ i:Fin (D+1), tune G i.val p j)/ ‖(1:G.Mat)‖ -- b unused remove
lemma payBig (i₀:ℕ)(h:i₀ ≤ D0) (p j:ℕ): 0 ≤ payT G D0 p j ∧ max (Multi.Maquette.upper (localSection G i₀)) (Next.Foundations.price G (i₀+p+j)) ≤ slotPay G (payT G D0 p j) b j p:=by
    have hv(i:ℕ) : 0 ≤ tune G i p j:= (zero_le_one.trans (Next.Foundations.price_one_le _ _)).trans (le_max_right ..)
    have hz:0 < ‖(1:G.Mat)‖:=by rw [Gauge.unitary_frob (show (1:G.Mat)* Star.star (1:G.Mat)=1 by simp)]; exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr G.dimPos)
    have hh:= Finset.single_le_sum (f:=fun i:Fin (D0+1)=> tune G i.val p j) (fun i _=> hv i.val) (Finset.mem_univ (⟨i₀,Nat.lt_succ_of_le h⟩:Fin (D0+1))); have he:0≤payT G D0 p j:= div_nonneg (Finset.sum_nonneg (fun i _=> hv _)) hz.le
    refine ⟨he,hh.trans ?_⟩; unfold slotPay; rw [← mul_assoc,payT,div_mul_cancel₀ _ hz.ne']; exact le_mul_of_one_le_right ((hv i₀).trans hh) (one_le_pow₀ (le_add_of_nonneg_right (by have h:=G.colorScale_pos; positivity)))
local notation "p"=> P.power
local notation "k0"=> P.order
local notation "J"=> payT G D0 P.power P.order
local notation "t0"=> slotPay G J b P.order P.power
variable (R:Side)(hR:∀ k≤D0,∀ (n:Side)(x:Site n), (localSection G k).footprint x⊆ neighbors b x)
open Org PhysicalNext.Repeat.Mallow
local notation "T₀" x=> (betaF G x R)
-- heights.Ages.Field. Powers paid for β
local notation "O'" i=> localSection G i
structure Etes (G:Gauge)(D b M CB:ℕ)(μ ζ κ:ℝ)(i:ℕ)(R:Side)(P:Stage)(x:ℝ):Prop where
     cash : Poster G R b M CB (payT G D P.power P.order) μ ζ κ P i x
     lights (k:ℕ)(he:k≤D)(n:Side)(t:BudgetPoint) (ht:t.threshold=temp (betaF G x R))(hj:t.order=P.order)(hp:t.power=P.power) (h1:2*(b+1) < n.val) (h2:2*(2*b) ≤ n.val) (o:Site n)(v: (Labels.frames G|>.level k).Coeff) (g:Grove o)(hX:(Labels.frames G|>.level k).coeffSize v ≤ (betaF G x R)^μ):
                let u:= (localSection G k).places v o
                let z:= argL G k i o g b κ v
                let S:= neighbors (b+1) o; let y:= betaF G x R; let f:= slotPay G (payT G D P.power P.order) b P.order P.power
                t.Regular S u ∧ t.supBounds o S u (y^μ*f) ∧t.Regular S z ∧ t.supBounds o S z (y^μ*(f+y^(-ζ))) ∧ t.Regular S (u-z)∧ t.supBounds o S (u-z) (y^μ*y^(-ζ)) ∧ ∀ V,‖u V‖≤ y^μ*f
include hR hv he hμ hκ
lemma encomia : ∀ᶠ x in atTop, Etes G D0 b M CB μ ζ κ i R P x:=by
    have hv(k:Fin (D0+1))(j:(Labels.frames G|>.level k.val).Index):= Sect.accrual G k.val i b κ j (j:=k0) («p»:=p) ζ hκ hv
    filter_upwards [(Work.E09.betaF_growth G R).eventually (eventually_all.mpr (fun k:Fin (D0+1)=>eventually_all.mpr (hv k))), PhysicalNext.Repeat.Mallow.castle R b M CB J μ ζ κ P i hκ (Sect.payBig G D0 b D0 le_rfl _ _|>.1) hμ he ‹ζ < (i:ℝ)/4›|>.and ((Work.E09.betaF_growth G R).eventually_ge_atTop 1)] with x H hh
    refine ⟨hh.1,fun k he n t ht hj hp h1 h2 o v g hX=>?_⟩ -- y x not x -> hx passed formula. H event at x not at shift
    let u:= (localSection G k).places v o; let z:= argL G k i o g b κ v
    let S:= neighbors (b+1) o; let y:= betaF G x R; let f:= t0
    have hw:0≤ y:= zero_le_one.trans hh.2; let K:= (⟨k, Nat.lt_succ_of_le he⟩:Fin (D0+1))
    have hg:= (Sect.payBig G D0 b k he p k0).2
    have hC:Next.Foundations.price G (k+p+k0) ≤ f:= (le_max_right ..).trans hg; have htC:(Multi.Maquette.upper (localSection G k)) ≤ f:= (le_max_left ..).trans hg
    have hz:0 ≤ f:= (zero_le_one.trans (Next.Foundations.price_one_le ..)).trans hC; have hy :0 ≤ y^(-ζ):= Real.rpow_nonneg hw _
    let τ:= y^(-ζ)
    have hN(j:(Labels.frames G|>.level k).Index):= Sect.blue G k o b j t hp hj (hR k he _ _) hC -- shadow
    obtain ⟨h,h',ha,hZ,hK,hu⟩:= Sect.sway G k i o g b κ v t f τ (fun j=> ⟨(hN j).1,(hN j).2, Sect.woods G k i o b κ j g t hp hj (hR k he _ _) hκ (H K j t hj hp ht n h1 h2 o (hR k he _ _) g) hC⟩)
    -- annotate `H` maybe m.P.hH.
    let L(φ:Config G n→ℂ)(e e':ℝ)(h:t.supBounds o S φ e)(he:e ≤ e') : t.supBounds o S φ e':=⟨h.1.trans he,fun U hp v hv hy=>(h.2 U hp v hv hy).trans he⟩
    exact ⟨h,L _ _ _ h' (mul_le_mul_of_nonneg_right hX hz),ha,L _ _ _ hZ (mul_le_mul_of_nonneg_right hX (add_nonneg hz hy)),hK,L _ _ _ hu (mul_le_mul_of_nonneg_right hX hy), Sect.heft G k o v _ _ hX (fun i V=> (YM.Multi.Maquette.purposes _ i|>.2 _ _).trans htC)⟩ -- inspect
end YM.LocalLTE.Port.Sect
