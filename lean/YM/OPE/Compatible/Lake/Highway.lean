import YM.OPE.Compatible.Lake.Dock
/-!
# Assembling the lane theorem. Requires physical procurement of data NOT done by weak estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction ContinuousLinearMap Treaty
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {d k i:ℕ}{H: Extraction.Order}{W:Table C.book} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)] [∀ i,FiniteDimensional ℂ (E i)]
local notation "V"=> C.label d
local notation "M"=>Dock E
variable {U r:ℕ→ℝ}{F:ℕ→ V≃L[ℂ]V}{c t:ℝ}{T:C.Makes}
structure Ferried (k:ℕ) (c:ℝ)(U r:ℕ→ℝ)(d:ℕ)(F:ℕ→ C.label d≃L[ℂ]C.label d) (E: Fin (d+1)→Type)[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℂ (E i)] (W:Table C.book):Prop where
   probe : ∃ p:ℕ→ C.label d→L[ℂ] Dock E, ∀ i:ℕ,k≤ i→Parcel W (F i) (p i) (U i) (r i) ∧ Crossing (F i) (F (i+1)) (p i) (p (i+1)) c i (U i) (r i)
lemma hop (x:ℕ→ℝ) {a:ℝ} (h:G.Simple) (hp:RateLE atTop (hill C) x a): RateLE atTop (hill C) (fun i=> x (i+1)) a:=by
   intro r hr; obtain ⟨v,hv,he⟩:= exists_between hr
   have hz(i:ℕ) : v * hill C (i+1)= v* hill C i+v*levy C i:=by unfold levy; ring
   have hh:= ((hill_high (C:=C) h).const_mul_atTop (sub_pos.mpr he)).eventually_ge_atTop 1
   have hT: Tendsto (fun i=>v*levy C i) atTop (𝓝 0):=by simpa only [mul_zero] using (taxes h).const_mul v
   filter_upwards [(tendsto_add_atTop_nat 1).eventually (hp v hv),hh,hT.eventually (ge_mem_nhds zero_lt_one)] with i hi hm hw
   apply hi.trans (Real.exp_monotone ?_); rw [hz]; linarith
-- abr sliding
lemma fees (L w L' w':ℕ→ℝ)(hG:G.Simple)(hL:RateLE atTop (hill C) L 0)(hL':RateLE atTop (hill C) L' 0)(ht:t ≤ 0)(hw:RateLE atTop (hill C) w t)(hw':RateLE atTop (hill C) w' t) :
    RateLE atTop (hill C) (fun i=> stampErr (L i) (L i) (L' i) (w i) (w' i) (w i)) t:=by
   have hp:= hill_high (C:=C) hG
   have he {a b:ℕ→ℝ}(u:RateLE atTop (hill C) a 0)(v:RateLE atTop (hill C) b t): RateLE atTop (hill C) (fun i=> adjustment (a i) (b i)) t:=by
      have hT:RateLE atTop (hill C) (fun i=>1+a i*(2*(a i+b i))) 0:=by
         have hk: RateLE atTop (hill C) (fun i=>a i*(2*(a i+b i))) 0:=by simpa only [zero_add] using u.mul ((RateLE.const 2 hp).mul (u.add (v.mono ht) hp))
         exact (RateLE.const 1 hp).add hk hp
      simpa only [adjustment,add_zero] using v.mul hT
   have hh:RateLE atTop (hill C) (fun i=>adjustment (L i) (w i)*L i) t:=by simpa using! (he hL hw).mul hL
   have hC:RateLE atTop (hill C) (fun i=>L i*adjustment (L' i) (w' i)) t:=by simpa using! hL.mul (he hL' hw')
   simpa only [add_zero,stampErr] using ((hh.add hw hp|>.add hC hp)|>.mul hL')
variable (Hc : Module.finrank ℂ (W.Field d)=Module.finrank ℂ (Dock E))
lemma ferryman {uF:ℕ→ C.label d ≃L[ℂ] C.label d} (hF : Ferried k c U r d uF E W) (hr:∀ i:ℕ,k≤ i→ 0≤ r i) {j:ℕ}(hk:k≤ j)
   (hv:∀ i:ℕ,j≤ i→ r i * U i<1/2)
   (Hc:Module.finrank ℂ (W.Field d)=Module.finrank ℂ (Dock E)) (ha:∀ i:ℕ,j≤ i→ stampErr (U i) (U i) (U (i+1)) (r i) (r (i+1)) (r i)*U i ≤1/2): ∃ P:ℕ→W.Field d≃L[ℂ]Dock E, Fiat C W (fun i=> 2*(U i+r i)+((Fintype.card (C.labels.level d).Index):ℝ)*U i) j uF P ∧ ∀ i:ℕ,j≤ i→ Bridge ((P (i+1)).symm.trans (P i)) C c (U i) (stampErr (U i) (U i) (U (i+1)) (r i) (r (i+1)) (r i) *(1+2*U i^2)) i:=by
   obtain ⟨p,hP⟩:=hF.probe
   have he(i:ℕ)(h:j ≤ i):∃ t,Remit W (uF i) (p i) (U i) (r i) t:=((hP i (hk.trans h)).1).remit (hr i (hk.trans h)) (hv i h) Hc
   have hN: Nonempty (W.Field d≃L[ℂ]Dock E):=Nonempty.intro (Classical.choose (he j le_rfl)); choose! A hA using he
   have hd(i:ℕ)(h:j≤ i):0 ≤ U i:=(norm_nonneg _).trans (hP i (hk.trans h)).1.reachNorm
   refine ⟨A,⟨fun i hi v=>?_,fun i hi x=>?_⟩,fun i hi=>gearbox (hP i (hk.trans hi)|>.2) (hA i hi) (hA (i+1) (by omega)) (ha i hi)⟩
   · have ht: 0 ≤ U i+r i := add_nonneg (hd i hi) (hr i (hk.trans hi)); let t:= (A i).toContinuousLinearMap.comp (covey W (uF i));
     have heq:‖t (uF i v)‖≤_:= (t.le_opNorm _).trans (mul_le_mul ((hA i hi).sizing) (Size.norm_le _ ((uF i) v)) (norm_nonneg _) (show 0≤2*(U i+r i) by positivity))
     rw [show t (uF i v)=A i (W.project d v) by simp [t,covey]] at heq; exact heq.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hd i hi))) (Work.G08.size_nonneg ..))
   obtain ⟨b,-,hb,hT⟩:= (hA i hi).supply
   refine ⟨(uF i).symm (b x),?_ ,?_⟩
   · have he:(A i).symm x=W.project d ((uF i).symm (b x)):=by
         change (A i).symm.toContinuousLinearMap x=_; rw [hT]; rfl
     rw [← he]; exact (A i).apply_symm_apply x
   dsimp only [chargeTerm]; rw [(uF i).apply_symm_apply]; apply (Size.le_norm _ _).trans
   apply (mul_le_mul_of_nonneg_left ((b.le_opNorm x).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) (by positivity)).trans
   rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   exact (le_add_of_nonneg_left (show 0 ≤ 2*(U i+r i) from mul_nonneg (by norm_num) (add_nonneg (hd i hi) (hr i (hk.trans hi))))).trans (Real.le_norm_self _)
-- toes
end YM.OPE.Lake
