import YM.OPE.Levy.Anchor
import YM.Pert.FirstTarget
/-!
# Coupled corrected trajectory at all engineering weights

Preserves the full-hierarchy weak comparison.
The proof is an adaptation of `Next.UVStress.Stations.equivalences`
with complete cutoff receipts for quotient-planes. No rate is asserted sharper
than o(log inverse length) in the exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress
open Bid Dash Next.Extract Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G} {S:Table C.book}{V:DiffPlan (Bel C.book)}{W:DiffPlan S} {H:S.Hierarchy}{a:(Bel C.book).Hierarchy}

-- Null against previous lifts preserved through every adjustment
lemma adj_anchored (Z:Zoom) (U:ℕ → Panel S) (R:Drop (Bel C.book)) (H:S.Hierarchy)(h:Anchored W Z U)(hv:W.Inclusions S):Anchored W Z (fun i=> corrected W V R (U i)):=by
   intro d
   have ht₀:=zlarge Z
   induction d with
   | zero => exact fun e he x φ hf => h _ e he x φ hf
   | succ d ih =>
       intro e he x φ hf
       have hA:= h _ _ he (x-adjStep V d (R d x)) φ hf
       have h_: d.succ ≤d+1:=le_rfl
       let ψ:=φ.comp (adjStep W d)
       have hm(i):φ (adjStep W d (corrected W V R (U i) d (R d x))+U i d.succ (x-adjStep V d (R d x))) = ψ (corrected W V R (U i) d (R d x)) + φ (U i d.succ (x-adjStep V d (R d x))):=map_add _ _ _
       change RateLE _ _ (fun i=>φ (corrected W V R (U i) d.succ x)) (-(e:ℝ))
       simp_rw [correction,hm]
       refine RateLE.add ?_ hA ht₀
       rcases eq_or_lt_of_le he with rfl|he'
       · have hf:∀z:S.Field d,ψ z=0:=fun z=>hf _ (LinearMap.mem_range.mpr ⟨z,rfl⟩)
         simpa only [hf] using RateLE.zero atTop (zstamp Z) (-(d.succ:ℝ)) (X:=ℂ)
       refine ih e (Nat.le_of_lt_succ he') _ _ (fun y hy=>?_) -- clarify let ψ
       have lt':=Nat.le_of_lt_succ he'
       cases e with
       | zero =>
          change y∈(⊥:Submodule ℂ _) at hy; rw [Submodule.mem_bot] at hy; subst y; exact map_zero _
       | succ j =>
          have hj:= Nat.le_of_succ_le lt'
          obtain ⟨z,rfl⟩ := (show y∈LinearMap.range (W.rise hj) from hy)
          change φ (W.rise _ _)=_
          rw [W.transit H.laws.toSymmetric hv]
          exact hf _ (show _∈LinearMap.range (W.rise _ ) from ⟨_,rfl⟩)

variable {F:Order}{B Z'}{A:Table C.book}{V':DiffPlan S}(L:Base C F A B Z' S V') (hq:RoughFactory C) (hs:Stocked C F) (hO:F.Ordered C S)(hPt:F.PointLimits C S)(hg:G.Simple)
include L hq hs hO hPt hg
theorem equivalences (H : S.Hierarchy) (a : (Bel C.book).Hierarchy)
    (hW : W.Inclusions S) (hp : W.Orientation H.spin)
    (hV : V.Inclusions (Bel C.book)) (hf : V.Orientation a.spin) (dim : DimAbove S) :
    ∃ X : Scaling S, Approaches (path X) (isoPanel X) ∧ Stable H.spin a.spin W V X ∧ Anchored W (path X) (isoPanel X) := by
  classical
  obtain ⟨x,U,hU,hy,ha,hpA⟩ := anchored_supply (H:=H) L hW hg hq hs hO hPt a
  choose R hR hb hr using fun d => signed_section (H:=a) (Nat.le_succ d) hV hf
  let Q k := corrected W V R (U k)
  have hu d := solid (H:=H) (a:=a) U hp hf R hb hr hU d
  have ha : Approaches x Q := adjusts H a hW hV x R ha
  have he d : ∀ᶠ k : ℕ in atTop, Bijective (Q k d) := by
    filter_upwards [MeterTest.injects H.smooth a ha d] with k hk
    exact ⟨hk,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm (LinearMap.finrank_le_finrank_of_injective hk) (dim d))).1 hk⟩
  let M k d := if p : Bijective (Q k d) then LinearEquiv.ofBijective _ p else
    LinearEquiv.ofBijective _ (he d).exists.choose_spec
  let X : Scaling S := ⟨M,fun _ => 1,x.r,fun _ => one_pos,x.positive,x.shrinking,x.limits⟩
  have hX (d) : ∀ᶠ k in atTop, isoPanel X k d=Q k d := by
    filter_upwards [he d] with k hk
    dsimp only [isoPanel,X,M]; rw [dif_pos hk]; rfl
  have hv (k d e : ℕ) (h : d≤e) z : Q k e (V.rise h z)=W.rise h (Q k d z) :=
    balanced H a _ hW hV R hR d e h z
  refine ⟨X,⟨fun n v => ?_⟩,fun_kit hu hX hv (fun _=>?_),?_⟩
  · refine (ha.values n v).congr (fun k => (smoothZoom H.smooth _ (X.positive k)).sub (smoothDisc a.smooth v)) ?_
    filter_upwards [eventually_all.mpr (fun i : Fin n => hX (v i).1)] with k hk
    intro y _; change tested _ _ _ _ - _ = tested _ _ _ _ - _
    unfold tested; rw [show (panels (Q k) ∘ v)=panels (isoPanel X k) ∘ v from funext (fun i => by
      change Sigma.mk (v i).1 (Q k _ _) = Sigma.mk (v i).1 (isoPanel X k (v i).1 (v i).2)
      rw [hk])]; rfl
  · simpa only [Q,corrected] using hy _
  have hq:= adj_anchored (V:=V) x U R H hpA hW
  intro d e he v φ hp
  apply RateLE.congr (hq d e he v φ hp) ((hX d).mono fun i hi=> (?_))
  rw [hi]
where
  fun_kit {Q : ℕ → Panel S} {X : Scaling S} (hq : ∀ d, ∀ᶠ k in atTop, StraightAt H.spin a.spin (Q k) d)
      (hX : ∀ d, ∀ᶠ k in atTop, isoPanel X k d=Q k d)
      (hp : ∀ k d e : ℕ, ∀ h : d≤e,∀ z,Q k e (V.rise h z)=W.rise h (Q k d z))
      (hu : ∀ k,Q k 0 ((Bel C.book).unit 0)=S.unit 0) : Stable H.spin a.spin W V X := by
    refine ⟨fun d => ?_,fun d e h => ?_,fun d => ?_⟩
    · filter_upwards [hX d,hq d] with k hk ht
      constructor
      · intro h x
        change (isoPanel X k d) _= S.mirror _ _ _ ((isoPanel X k d) _)
        rw [hk]; exact ht.reflects ..
      intro x; change (isoPanel X k d) _= S.conj _ _ ((isoPanel X k d) _)
      rw [hk]; exact ht.bars ..
    · filter_upwards [hX d,hX e] with k hk he v
      change (isoPanel X k e) _=W.rise h ((isoPanel X k d) _)
      rw [he,hk,hp]
    filter_upwards [hX d] with k hk
    change (isoPanel X k d) _=_
    let h := Nat.zero_le d
    rw [hk,← V.fixs hV a.laws h,hp,hu,W.fixs hW H.laws h]

end YM.OPE.Levy
