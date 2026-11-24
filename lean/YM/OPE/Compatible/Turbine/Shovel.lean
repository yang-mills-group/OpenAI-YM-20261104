import YM.OPE.Compatible.Turbine.Crank
import YM.OPE.Compatible.Turbine.Wagon
/-! Linear beam cart exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives)(u:X)
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "K!"=> Arboreal.trim U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=>glen D U u
variable (p:X→ S.Tag)(hu:u∈ rest U){b d:ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ S.Tag)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hh:1 ≤ b)(hb:d ≤ b)
variable (ht:∀ᶠ i in φ, whenHigh U (schedule C b (η/2) (s i))=schedule C b (η/2) (s i) u∧ aperture D C b 2 (η/2) (r i) (s i) u ≤ schedule C b (η/2) (s i) u-1)
variable {x:I→X→E4} (hx:∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥)))
local notation "O!" => fun i=> x i ⊥
local notation "X!"=> fun i=>away (x i) (x i ⊥)
local notation "Z!"=>fun i=>away (z i) (x i ⊥)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "P₀"=> Ward.expose ∘ p
variable (hy:∀ᶠ i in φ, ClearOf (x i ⊥) (z i) c)
local notation "V₀"=> picked V
local notation "P!"=> P.ope
local notation "g"=>fun (b:Mode L) i=> P.ope b (picked Θ (x i)) (picked Θ (Ward.expose∘p)) (x i u)
local notation "K₁"=> fun (d:ℕ) i=> shortInk D U p₀ u (s i) d
local notation "K₂"=>fun (d n:ℕ)i=> tallInk D U p₀ u (s i) d n
-- signed mixed, at exact d for entire levels
local notation "C!" => fun i c=> frontierCoefficient D T K! c (s i) (x i)
local notation "S!"=> fun i c => shoot D T U u c (s i) (x i) p
variable (c':Tones T)
local notation "ℜ"=> fun i=>trunc T d (s i u) (picked Θ (x i)) (picked Θ p) (x i u)
local notation "ℜ'"=> fun i=>shadow P d (picked Θ (x i)) (picked Θ P₀) (x i u)
local notation "k"=> c'.fst
local notation "M'"=> shades (facets T)
local notation "q"=>fun (z:S.Field d)=>update p u (⟨d,z⟩: S.Tag)
include H' A Y hO hu hx hη hM
omit H' A hO hM in
lemma zone_shift (d:ℕ): ∀ᶠ i in φ,∀ a∈ shades (facets T) d,C! i c' (update p u (⟨d,(legends T).there d a⟩: S.Tag))=C! i c' (paint T u p a):= by
    have hp:= Burst.crown D Y; have hU: u∈ H:= (frontier_trim D U hp ((rest_mem ..).1 hu|>.1) ((rest_mem ..).1 hu|>.2)).2 (Or.inl rfl);
    filter_upwards [casing D (S:=S) Y hη (filter_subset ..) (remains U hp ((rest_mem ..).1 hu|>.1)) hx] with i hi b hb
    letI : DecidableEq H:= fun _ _=> Classical.propDecidable _; unfold frontierCoefficient paint; rw [paintable D p hU,paintable D p hU,Catalogue.present _ _ _ (shadows ..|>.mp hb)]; exact beam_steps T (picked H p) _ hi c' ((shadows ..).1 hb) ((legends T).axis b) ⟨u,hU⟩
include h
lemma haul_secs (F:I→ S.Field d→ₗ[ℂ]ℂ) (hF:∀ᶠ i in φ,∀ v:S.Field d, frontierCoefficient D T K! c' (s i) (x i) (q v)=F i v) : PaidWeight φ r (K₀ k) (fun i=> F i (ℜ i- ℜ' i)):=by
    let w b:= (legends T).there d b; let W b:= (legends T).readIn d b; let V' i:= ℜ i-ℜ' i; let W':= bands T.sector.derivatives d
    have hg:= Burst.life D Y; have he:= atProfits D u P₀ (d:=d) (n:=k) hu Y; have h1:∀ᶠ i in φ,0 ≤ K₁ d i:= he.mono fun i hi=>hi.2.1.le; have h2:∀ᶠ i in φ,0 ≤K₂ d k i:= he.mono fun i hi=>hi.2.2.le
    have hZ :PaidWeight φ r (K₁ d) V' :=by
        have hh:=(Y.fresh _ hη).fade u ((rest_mem ..).1 hu|>.2); refine (glen_prime D T P u p hu Y H' hO A h hη hM hx d).monoWeight h1 ?_
        filter_upwards [h1,hh.eventually self_mem_nhdsWithin,(hh.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one)] with i hi ht hz
        have ht':0<s i u:=ht
        let v:= area D p₀ (s i) (cove D U u)
        have hx:0≤ v:=nonneg_of_mul_nonneg_left (by rw [← div_eq_mul_inv]; exact hi) (inv_pos.mpr (pow_pos ht' d))
        exact div_le_div_of_nonneg_left hx (pow_pos ht' _) (pow_le_pow_of_le_one ht'.le hz (Nat.le_succ d))
    apply (PaidWeight.ascaled (he.mono fun _ hi=>hi.1.le)).2
    have ht1 :∀ i,F i (V' i)= ∑ b∈ M' d,(W b) (V' i) • F i (w b):=by
       intro i; conv_lhs=> rw [← (legends T).encode T.room.kernel.laws.toSymmetric T.phase.transport.injection _ (V' i),map_sum]; exact sum_congr rfl fun b _=> map_smul ..
    change Score φ r (fun i=> (↑(K₀ k i):ℂ) • F i (V' i))
    simp_rw [ht1, Finset.smul_sum]; apply Score.summar _ _ hg; intro b _
    have hA:= (PaidWeight.ascaled h2).1 ((prime_load D T u p hu Y H' hO A hη hM hx c' ⟨d,w b⟩).alter (show _ =ᶠ[φ] (fun i=>F i (w b)) from hF.mono fun i hi => hi (w b)))
    have hB := (PaidWeight.ascaled h1).1 (hZ.applyLinear h1 hg (W b) (W b).continuous_of_finiteDimensional); refine (hB.dot hA).congr ?_; filter_upwards with i; change ((↑(K₁ d i):ℂ) * ((W b) (V' i))) * ((↑(K₂ d k i):ℂ)* (F i (w b)))=(↑(K₀ k i):ℂ)* (_ * _)
    have hk: K₀ k i= K₁ d i*K₂ d k i := reloaded D u P₀ _ _ _; rw [hk, Complex.ofReal_mul]; ring
include hh ht hb
lemma tower_pays : PaidWeight φ r (K₀ k) (fun i=> frontierCoefficient D T U c' (s i) (x i) p-∑ b∈ M' d,S! i b*C! i c' (paint T u p b)):=by
    obtain ⟨L',hL'⟩ := prime_cart D T u p hu Y hη hx c' d; refine ((vehicle D T P u p hu Y H' hO A h hη hM hh hb ht hx c').sub (haul_secs D T P u p hu Y H' hO A h hη hM hx c' L' hL') (by filter_upwards [atProfits D u P₀ (d:=d) (n:=k) hu Y] with i hi using hi.1.le) (Burst.life D Y)).alter ?_
    filter_upwards [hL', zone_shift D T u p hu Y hη hx c' d] with i hi hm; rw [map_sub]
    have he : L' i (ℜ i)= ∑ b∈ M' d, S! i b*C! i c' (paint T u p b):=by
       dsimp only; unfold trunc; rw [map_sum]; refine sum_congr rfl fun b hb=>?_ ; rw [map_smul,← hi]; exact congr_arg (fun t:ℂ=>S! i b * t) (hm b hb)
    have hx : L' i (ℜ' i)= ∑ b∈ bands L d, P.ope b (picked Θ (x i)) (picked Θ P₀) (x i u) * frontierCoefficient D T K! c' (s i) (x i) (update p u (⟨d,P.loaded b d⟩: S.Tag)):=by
       dsimp only; unfold shadow; rw [map_sum]; refine sum_congr rfl fun b hb=>?_ ; rw [map_smul,hi]; rfl
    dsimp only at *; rw [he,hx]; abel
end YM.OPE.Arboreal.Trace
