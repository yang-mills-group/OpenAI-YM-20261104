import YM.OPE.Compatible.Lux.Credit
/-!
# Full real single readout accordingly, costed at latest currencies
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Table MeasureTheory Cov Display Survey Trace
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
   {I J V:Type}[Fintype J][Fintype I][PartialOrder I][OrderBot I]
variable (D:Origin I){Q:Finset I}(A:Allot C)(hL:Lanes (F:=F) U.sector.derivatives)(hs:Services C F S)
variable {ψ:Filter V}{T: V→ℝ}{s:V→I→ℝ}{η M c:ℝ} {x:V→I→E4}(H: Burst D Q ψ T s)
variable (hx:∀ᶠ i in ψ,Ridge (s i) η M D Q (away (x i) (x i ⊥)))(hη:0<η)(hM:0 ≤ M)
variable (p:brim D Q→ S.Tag)(y: V→J→ E4)(q:J→ S.Tag)(v:V→Viewers U)
variable {P:Prescription U.sector.derivatives}(hP:P.Coherent)
local notation "k"=> brim D Q
set_option quotPrecheck false
local notation "o"=> fun i=> x i ⊥
local notation "Y" => fun i=> picked (brim D Q) (x i)
local notation "B!"=>fun i=>s i ⊥
local notation "Z"=> fun d i=> costed D Q d (Sigma.fst∘p) (s i)
include H A hL hs hx hη hM
include hP in
lemma ray_tracks (d:ℕ): PaidWeight ψ T (Z (d+1)) (fun i=> ray U d (Y i) p (o i)-shadow P d (Y i) (Ward.expose ∘ p) (o i)) :=by
    obtain ⟨he,hi⟩:=finish_view D H hx hη (Finset.Subset.refl Q) (Burst.crown D H); refine approximate U (Burst.life D H) ((cost_pos D H p (d+1)).mono fun _ h=>h.le) he hi (fun I _ w u c hc h=>?_); exact era_shadow U D A hL hs H hx hη hM p u w (fun _=>none) P hP d h hc
lemma earns_lens (w:Tones U): PaidWeight ψ T (Z w.fst) (fun i=> lens U w (Y i) p (o i)) :=by
    obtain ⟨P,hp⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection; let V:= legends U; let n:= w.fst; let W:= V.readIn n w; have ht:= Burst.life D H; have hc:∀ᶠ i in ψ,0 ≤ Z n i:= (cost_pos D H p n).mono fun _ h=>h.le
    have ho := (H.fresh _ hη).fade _ (Burst.crown D H|>.base); let q:= Ward.expose ∘ p
    have hW: ∀ᶠ i in ψ,Z n i ≤ Z (n+1) i:=by
       filter_upwards [hc,ho.eventually self_mem_nhdsWithin,(ho.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one)] with i hh hi he; change 0 ≤ _ / s i ⊥ ^ n at hh; have hp:0 < s i ⊥ := hi; let a:=volume D Q (Sigma.fst∘p) (s i); have hq:0 ≤ a:= nonneg_of_mul_nonneg_left (by rw [← div_eq_mul_inv]; exact hh) (inv_pos.mpr (pow_pos hp n)); exact div_le_div_of_nonneg_left hq (pow_pos hp _) (pow_le_pow_of_le_one hp.le he n.le_succ)
    have he:= ((ray_tracks U D A hL hs H hx hη hM p hp n).monoWeight hc hW).applyLinear hc ht W W.continuous_of_finiteDimensional
    have hv: PaidWeight ψ T (Z n) (fun i=> W (shadow P n (Y i) q (o i))) :=by
       apply (PaidWeight.ascaled hc).2; unfold shadow; simp_rw [map_sum,Finset.smul_sum,map_smul]; apply Score.summar _ _ ht; intro i hi
       have hf:i.fst≤ n:= (full_bands ..).1 hi; rcases hf.eq_or_lt with h|h
       · have hx:= earns U D A hL hs H hx hη hM p P hp i; rw [h] at hx; have he:= (PaidWeight.ascaled hc).1 hx
         exact ((he.dot (Score.steady (W (P.loaded i n)) ht))).congr (Eventually.of_forall fun u=> smul_assoc ..)
       have hb: (facets U).part w.fst n (P.loaded i n)=0:= by rw [P.cost _ hi, MultipleContact.Splitting.part_rise (facets U) U.room.kernel.laws.toSymmetric U.phase.transport.injection hf,MultipleContact.Splitting.beyondZero (facets U) h,LinearMap.zero_apply]; -- then
       have h': W (P.loaded i n)=0:= Eq.trans (V.readIt n w _) ((congr_arg ((V.axisSet n).coord w.snd) (Subtype.ext hb)).trans (map_zero _)); simp_rw [h',smul_zero]; exact Score.steady _ ht
    refine (he.add hv hc ht).alter ?_; filter_upwards with i; rw [map_sub,sub_add_cancel]; rfl
variable [ψ.NeBot]
lemma earns_screen (d:ℕ)(hc:0<c)(hf:∀ᶠ i in ψ, ClearOf (x i ⊥) (y i) c): PaidWeight ψ T (Z (d+1)) (fun i=> kernel (spectator U (v i)) (beside (Y i) (y i)) (beside p q)-Cov.insert S (spectator U (v i)) (o i) (y i) q d (ray U d (Y i) p (o i))) :=by
    obtain ⟨P,hp⟩:=Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection; have ht:= Burst.life D H; have he:∀ᶠ i in ψ,0≤ Z (d+1) i:= (cost_pos D H p _).mono fun _ h=> h.le
    have hL':= adj_cost U ht he hs q v y hc hf (ray_tracks U D A hL hs H hx hη hM p hp d); refine ((era_shadow U D A hL hs H hx hη hM p y q v P hp d hf hc).sub hL' he ht).alter ?_; filter_upwards with i; rw [map_sub]; abel
end YM.OPE.Arboreal
