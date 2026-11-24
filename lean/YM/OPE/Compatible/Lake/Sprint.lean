import YM.OPE.Compatible.Lake.Bloom
/-!
# Price after projections
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction ContinuousLinearMap Treaty
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {H:Extraction.Order}{W:Table C.book}
variable {d k:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I"=> Fin (d+1)
variable {a U r:ℕ→ℝ} {c t:ℝ}
variable (h:G.Simple)(hA:RateLE atTop (hill C) a c)(hC:0≤t) (hU: RateLE atTop (hill C) U 0) {δ:ℝ} (hr:RateLE atTop (hill C) r (-1-δ))(he:0<δ)
local notation "L"=> C.label d
structure Fiat (C:Family G)(W:Table C.book) (a:ℕ→ℝ)(k:ℕ)(R:ℕ→C.label d≃L[ℂ]C.label d)(J:ℕ→W.Field d≃L[ℂ]Dock E) :Prop where
   head m : k ≤ m→∀ v:C.label d, ‖J m (W.project d v)‖ ≤ a m * chargeTerm d v (R m)
   lift m : k ≤ m→∀ x: Dock E, ∃ v:C.label d, J m (W.project d v)=x∧ chargeTerm d v (R m) ≤ ‖a m‖*‖x‖
include h hA hC hU hr he
lemma extend_drive (W:Table C.book)(j:ℕ)(hx:∀ᶠ i:ℕ in atTop,16 ≤ extent C i): ∃ (k D:ℕ), j ≤ k ∧ ∀ (Q:ℕ→C.label d≃L[ℂ]C.label d)(J:ℕ→W.Field d≃L[ℂ]Dock E), Fiat C W a j Q J → (∀ i:ℕ,j ≤ i→ Bridge ((J (i+1)).symm.trans (J i)) C t (U i) (r i) i)→ ∃ Y:ℕ→W.Field d≃L[ℂ]Dock E, Coach C W k D E Q Y := by
   let s:= δ / ((d:ℝ)+1); have hs:0<s:=div_pos he (by positivity)
   obtain ⟨D,hD⟩:= sold (E:=E) h hU hC hr hs (by unfold s; field_simp; linarith)
   have hφ : RateIs atTop (hill C) (fun i=> Real.exp ((d:ℝ)*s*hill C i)) (d*s) := RateIs.exp _ (hill_high h)
   have hg := hA.norm.mul (hφ.pays (hill_high h))
   obtain ⟨M,hM⟩:=exists_nat_gt (c+d*s)
   let g := D+M; have he': c+d*s < g:= hM.trans_le (show (M:ℝ) ≤ g by unfold g; simp)
   have hu:= ((speck (C:=C)).power g).outweigh hg (by simpa only [mul_one] using he') (hill_high h)
   obtain ⟨k,hk⟩:= eventually_atTop.mp (((hx.and (eventually_ge_atTop j)).and hD).and hu)
   have hb := (hk k le_rfl).1.1.2
   refine ⟨k,g,hb,fun Q J hJ hR=>?_⟩
   let Y i:= (J i).trans (cram C E s i); have hZ (i:ℕ)(h:k ≤ i): ‖a i‖* Real.exp ((d:ℝ)*s*hill C i) ≤ β C i^g:=by
        apply le_trans (Real.le_norm_self _) (hk i h).2
   refine ⟨Y,⟨fun i hi=>?_⟩,fun i hi v=>?_,fun i hi x=>?_⟩
   · obtain ⟨hx,-⟩:= hk i hi; obtain ⟨⟨he,-⟩,hp⟩:= hx
     let V:=((J (i+1)).symm.trans (J i)); obtain ⟨a,b,P,hP,hQ,hB,hL,hC'⟩:= hp V (hR i (hb.trans hi))
     refine ⟨P,b,a,hP,he,hQ,hB,hL,hC'.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right ?_ (levy_pos h i|>.le)))⟩
     change (D:ℝ) ≤ (g:ℝ); unfold g; simp
   · apply (((cram C E s i).toContinuousLinearMap.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (sand C hs.le i|>.1))).trans; apply (hJ.head i (hb.trans hi) _).trans
     apply mul_le_mul_of_nonneg_right _ (Work.G08.size_nonneg ..); apply (Real.le_norm_self _).trans ((le_mul_of_one_le_right (norm_nonneg _) ?_).trans (hZ i hi))
     exact Real.one_le_exp (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hs.le) (hill_pos ..|>.le))
   let A := cram C E s i; obtain ⟨v,hv,hw⟩:= hJ.lift i (hb.trans hi) (A.symm x)
   refine ⟨v, show A (J i (W.project d v))=_ from ?_, hw.trans ?_⟩
   · rw [hv,A.apply_symm_apply]
   apply (mul_le_mul_of_nonneg_left ((A.symm.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right (sand C hs.le i|>.2) (norm_nonneg _))) (norm_nonneg _)).trans ?_
   rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hZ i hi) (norm_nonneg _)
end YM.OPE.Lake
