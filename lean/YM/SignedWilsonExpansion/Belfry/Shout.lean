import YM.SignedWilsonExpansion.Belle.Wipe
import YM.FVA2.Main
/-!
# Reaudition of independent position LPT at moving radii. Pre-position calculation

Includes first light through step, without asymptotic commits on chosen cutoff-phase
entries. All claims on Teaching.S real heights before character. Numerical conversion
on common tails uses relative Price and strict ROOT near branch, not a continuity assumption
on any public vote/name matrix.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Belfry
open Function Set Filter Asymptotics PowerSeries Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book MS.Book.Program MS.Book.Convolve MS.Puff MS.Puff.Actors
open XSpace XSpace.Structure1 XSpace.Normalize FVA2 FVA2.Scale FVA2.Reg FVA2.Dframe
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open Dancer Commission Belle Belle.Path Belle.Buffet Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{ι σ κ κ':Type}{n q m d:ℕ}{L:Filter ι}{θ ε g:ι→ℝ}
namespace ScaleFits
abbrev FO (L:Filter ι){K:Type}[Norm K](q:ι→K):= q=O[L](1:ι→ℝ)
variable (h:Tendsto θ L (𝓝 0)) {F' K:ι→Guard G d}{p:ι→Cn}{Q:ι→ Tape.Table (Sec G d) n}
local notation "H[" z "]" => FO L z
abbrev Budget (L:Filter ι)(F:ι→Guard G d): Prop:= ∀ b:ℕ,SeatsW.Salary ℂ L (1:ι→ℝ) (fun i=> coeff b (F i))
abbrev funds (L:Filter ι)(p:ι→Cn): Prop:= ∀ j:ℕ,(fun i=> coeff j (p i))=O[L](1:ι→ℝ)
abbrev castℂ (θ:ι→ℝ)(i:ι):ℂ:= θ i
abbrev Audit (L:Filter ι)(θ:ι→ℝ)(q:ℕ):=Taught L 1 θ 1 (castℂ θ) q
lemma accounts (k:funds L p): charge q L 1 1 p :=fun i _=> Wage.enroll (k i)
lemma castCost : castℂ θ=O[L] θ:= Wipe.earth_p (isBigO_refl ..)
include h
lemma castBound : FO L (castℂ θ):=castCost.trans ( Wipe.stop h )
lemma powers (b:ℕ): FO L (fun i=> (castℂ θ i)^b):= ((castBound h).pow b).congr_right fun i=> one_pow _
lemma low : ∀ᶠ i in L, |θ i|≤1:= h.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1)
lemma identity_clock (b:ℕ): Audit L θ b (fun _=> PowerSeries.X) (castℂ θ):=by
    have ht: charge b L 1 1 (fun _=> PowerSeries.X):= fun i _=> Wage.unitC _; constructor
    · exact ht
    · exact Wage.enroll (castBound h)
    apply Wage.enroll; by_cases hp:b=0
    · subst b; simp_rw [ timed, zero_add, Finset.range_one, Finset.sum_singleton, coeff_zero_X, zero_mul,sub_zero, pow_one,one_mul]; exact castCost
    have he(i:ι): calcT (θ i) b PowerSeries.X=(θ i:ℂ):=by
        rw [timed,Finset.sum_eq_single 1]; · simp
        · intro i _ hi; rw [coeff_X, if_neg hi,zero_mul]
        simp; omega
    change (fun i=> (θ i:ℂ)-calcT (θ i) b PowerSeries.X)=O[L] _; simp_rw [he,sub_self]; exact isBigO_zero ..
lemma amount (k:funds L p): Audit L θ q p (fun i=>calcT (castℂ θ i) q (p i)):=Taught.epoch awarded (low h) _ castCost (accounts k)
lemma soldSc {y:ι→Cn}{z:ι→ℂ}(p:Audit L θ q y z): (fun i=> z i-calcT (castℂ θ i) q ( y i ))=o[L]( θ^q ):= (unfoldW p.bill).trans_isLittleO ( by simp; exact Wipe.expense h IsEquivalent.refl (Nat.lt_succ_self q) )
lemma heeded {x:ι→ℂ}(H:Audit L θ q p x)(u:∀ i, Rooted (p i))(V:∀ j (v:Tags G d n),FO L (fun i=> Q i j v))(t:Tags G d n) : Audit L θ q (fun i=> Tape.archive (substitute (p i) (Q i)) t) (fun i=> invoke (Q i) q (x i) t):=by
    have H'(i):Tape.archive (substitute (p i) (Q i)) t=(Tape.archive (Q i) t).subst (p i):=Reg.Point.moves (Q i) t (u i)
    simp_rw [H']; exact Taught.shuffle awarded (low h) _ castCost H ( accounts (show funds L (fun i=> Tape.archive (Q i) t) from fun x=> by simp_rw [Tape.archive, coeff_mk]; exact V _ _)) (fun i=>(coeff_zero_eq_constantCoeff_apply _).symm.trans (u i))
omit h
lemma Budget.comp {D:Filter σ}(H:Budget L F')(x:σ→ι)(p:Tendsto x D L): Budget D (F' ∘ x):=fun i T=> (H i T).comp_tendsto p -- omit h
lemma funds.comp {D:Filter σ}(H:funds L p)(x:σ→ι)(u:Tendsto x D L): funds D (p ∘ x):= fun i=> (H i).comp_tendsto u
lemma chargeTheory (T: Tags G d n)(v:∀ k (x:Tags G d n),FO L (fun i=> Q i k x)): charge q L 1 1 (fun i=> Tape.archive ( Q i ) T):=accounts (p:=fun i=> Tape.archive ( Q i ) T) (fun x=>by simp_rw [Tape.archive, coeff_mk]; exact v ..)
-- projection order incl b=0
abbrev young (b:ℕ)(t:ℝ)(u:Guard G d): FieldEnd G d:= citeS b (t:ℂ) (Tape.facet u)

lemma young_apply (x:Sec G d)(t:ℝ)(F: Guard G d): (young q t F) x=citeS q (t:ℂ) ( Tape.spur ( Tape.facet F ) x ):=by
    unfold young citeS; repeat rw [LinearMap.sum_apply]
    rfl
include h
lemma paidYear (x:Tags G d n)(H:Budget L F') (pA:∀ k (x: Tags G d n),FO L (fun i=> Q i k x)) : Audit L θ q (fun i=> Tape.archive (Tape.horizon ( F' i ) (Q i)) x ) (fun i=> invoke ( Q i ) q ( castℂ θ i ) ( (young q (θ i) ( F' i )) ∘ x )):=by
    let α(i:ι)(j:Fin n):= Tape.spur ( Tape.facet ( F' i )) ( x j ); have hi (j:Fin n)(b:ℕ): Commission.Salary L 1 1 ℂ (fun i=> α i j b):=fun T=>Wage.enroll ((H b ( T ∘ₗ LinearMap.applyₗ _ ))); obtain z:= Taught.manifests (q:=fun _=> PowerSeries.X) Buffet.awarded (low h) (castℂ θ) castCost Q (fun _=> 1) α (identity_clock h q) (fun _=> by simp) (fun i=> chargeTheory i pA) (fun i k _=> hi i k); simp_rw [ Taught.ruler, Tape.composed_id, Finset.prod_const_one, Tape.horizon_spur,show ∀ i,young q (θ i) ( F' i ) ∘ x=_ from fun i:ι=> funext fun j=> young_apply (x j) (θ i) ( F' i ) ] at *
    exact z
end ScaleFits
end YM.SignedWilsonExpansion.Belfry
