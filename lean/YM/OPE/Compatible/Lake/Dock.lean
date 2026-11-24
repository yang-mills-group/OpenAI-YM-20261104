import YM.OPE.Compatible.Lake.Gulf
/-!
# Switch estimate. Only need evolved projection price on calibration. Measure transfer actual in this currency, use approximate reads.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction ContinuousLinearMap Treaty
open scoped Topology Classical BigOperators
variable {G:Gauge} {S:Schedule}{C:Family G}{d i:ℕ}{W:Table C.book} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "V"=> C.label d
local notation "M"=>Dock E
local notation "T"=> (LinearMap.toContinuousLinearMap (W.project d))
def covey (W:Table C.book) (A:V≃L[ℂ]V) :V→L[ℂ] W.Field d := LinearMap.toContinuousLinearMap (W.project d) ∘L A.symm.toContinuousLinearMap
abbrev adjustment (U ε:ℝ):= ε*(1+U*(2*(U+ε)))

-- Pi in realm
structure Parcel (W:Table C.book)(A:V ≃L[ℂ] V)(p:V→L[ℂ] M)(L ε:ℝ) :Prop where
     reachNorm : ‖p‖≤L
     supply : ∃ b:M→L[ℂ] V,p.comp b=ContinuousLinearMap.id .. ∧ ‖b‖≤L
     remove : ∀ x:(V), W.project d (A.symm x)=0 → ‖p x‖≤ε *‖x‖
structure Remit (W:Table C.book)(A:V ≃L[ℂ] V)(p:V→L[ℂ] M)(L ε:ℝ)(R:W.Field d≃L[ℂ] M) :Prop where
   supply : ∃ b:M→L[ℂ] V,p.comp b=ContinuousLinearMap.id .. ∧ ‖b‖≤L ∧ R.symm.toContinuousLinearMap=(covey W A).comp b
   sizing :‖R.toContinuousLinearMap.comp (covey W A)‖ ≤ 2*(L+ε)
   amends :‖p-R.toContinuousLinearMap.comp (covey W A)‖ ≤ adjustment L ε
lemma Parcel.remit [∀ i,FiniteDimensional ℂ (E i)] {p:V→L[ℂ] M}{A:V≃L[ℂ]V}{L ε:ℝ}(P:Parcel W A p L ε) (he:0 ≤ ε)(hr:ε*L<1/2)(hv:Module.finrank ℂ (W.Field d)=Module.finrank ℂ (Dock E)): ∃ R,Remit W A p L ε R:=by
   obtain ⟨b,hb,hB⟩:= P.supply; obtain ⟨t,ht,hg,hH⟩:= spansElite (f:=covey W A) P.reachNorm hB hb hv he hr P.remove; exact ⟨t.symm,⟨b,hb,hB,ht⟩,hg,hH⟩
abbrev stampErr (B L U ε r w :ℝ):=(adjustment L ε*B + w + B*adjustment U r)*U
def turnover (F J:V≃L[ℂ]V) : V≃L[ℂ]V:= J.symm.trans F
structure Crossing (F J:V≃L[ℂ]V)(p q:V→L[ℂ]M)(t:ℝ)(i:ℕ)(U ε:ℝ) :Prop where
   paycheck : ∃ R, Treaty (extent C i) (Real.exp (t*levy C i)) U (R:Dock E≃L[ℂ]Dock E) ∧ ‖p.comp (turnover F J).toContinuousLinearMap-R.toContinuousLinearMap.comp q‖≤ ε
   train : ‖(turnover F J).toContinuousLinearMap‖≤U
lemma gearbox {p q:V→L[ℂ] M}{F J: V ≃L[ℂ]V}{t B L U ε ε' w:ℝ}(h: Crossing F J p q t i B w)
   {R S': W.Field d≃L[ℂ] M} (H: Remit W F p L ε R)(Z:Remit W J q U ε' S')
   (hK : stampErr B L U ε ε' w *B ≤1/2) :
    Bridge (S'.symm.trans R) C t B (stampErr B L U ε ε' w * (1+2*B^2)) i:= by
    obtain ⟨Y,hY,hW⟩:= h.paycheck; obtain ⟨b,hb,hB,ht⟩:= Z.supply
    let Mv := turnover F J; let M' := Mv.toContinuousLinearMap
    let X:= R.toContinuousLinearMap.comp (covey W F)
    let X':= S'.toContinuousLinearMap.comp (covey W J)
    let T':=Y.toContinuousLinearMap; let a := stampErr B L U ε ε' w
    have hs: X.comp M'= R.toContinuousLinearMap.comp (covey W J):=by ext1; simp [X,M',Mv,covey,turnover]
    have he : (S'.symm.trans R).toContinuousLinearMap-T'=(X.comp M'-T'.comp X').comp b:=by
       rw [hs]; ext1 v
       change R (S'.symm v)-T' v=R (covey W J (b v))-T' (S' (covey W J (b v)))
       rw [show covey W J (b v) = S'.symm v from Eq.symm (show S'.symm.toContinuousLinearMap v=_ from by rw [ht];rfl), S'.apply_symm_apply]
    have hp:‖X.comp M'-T'.comp X'‖ ≤ adjustment L ε*B+w+B*adjustment U ε':=by
       have hx:= (opNorm_comp_le (X-p) M').trans (mul_le_mul (by rw [norm_sub_rev]; exact H.amends) h.train (norm_nonneg _) ((norm_nonneg _).trans H.amends))
       have hy:= (opNorm_comp_le T' (q-X')).trans (mul_le_mul hY.charge Z.amends (norm_nonneg _) ((norm_nonneg _).trans hY.charge))
       rw [show X.comp M'-T'.comp X'=(X-p).comp M'+(p.comp M'-T'.comp q)+T'.comp (q-X') by rw [sub_comp,comp_sub]; abel]
       exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hx hW)) hy)
    have hF : ‖(S'.symm.trans R).toContinuousLinearMap-Y.toContinuousLinearMap‖≤a:=by
       rw [he]; exact (opNorm_comp_le ..).trans (mul_le_mul hp hB (norm_nonneg _) ((norm_nonneg _).trans hp))
    have ha:0≤a:= (norm_nonneg _).trans hF
    refine ⟨Y,hY,hF.trans (le_mul_of_one_le_right ha (by have :=sq_nonneg B;linarith)),(inverse_diff _ _ hY.inverse hF hK).trans ?_⟩
    linarith only [ha]
end YM.OPE.Lake
