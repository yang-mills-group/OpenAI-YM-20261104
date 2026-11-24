import YM.OPE.Compatible.Satin.Gather
/-! scale profits for second argument and normalized functional. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)
    {P:Prescription T.sector.derivatives}{u:X}
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "B"=> bands L
local notation "H"=> brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=> glen D U u
variable (p:X→ C.book.Token)(hp:Crown U)(hu:u∈ rest U) {d:ℕ} {s:X→ℝ}
-- algebra on prices. Write Wv area over glen, P over trimmed W leaves; then product; cancellations exact. no need largest here.
local notation "p₀"=> fun i:V=> (p i.val).1
local notation "p'"=> fun (q:C.book.Token) (i:H)=> (pallet p q u i.val).1
local notation "k"=> cove D U u
include hu hp
lemma trimmed_units (a:C.book.Token) : volume D (Arboreal.trim U u) (p' a) s= s (par D u)^a.1*area D p₀ s (univ\cove D U u):=by
    let E(i:X):= s (par D i)^(p i).1; have ht:= cove_prod (U:=U) D u (fun i=>E i.val) (fun i=>E i.val) (fun i=>E i.val) (fun _=>rfl) (fun _=>rfl)|>.2
    let U':= update p u a; unfold volume area; rw [← Equiv.prod_comp (trails D U u hp hu),Fintype.prod_sum_type, Fintype.prod_unique]; change s (par D u)^(update p u a u).fst*(∏ i:shore D U u,s (par D i.val) ^(U' i.val).1)= _; rw [update_self u a p]; refine congr_arg _ (?_ : _=∏ i∈univ\ cove D U u,E i.val); rw [ht]; exact prod_congr rfl fun i _=> by unfold E U'; rw [update_of_ne (shore_ne D U u i.2)]
-- local fee. no need largest
omit hu hp in
lemma balance_units (n:ℕ)(a:C.book.Token): volume D U p₀ s*(s (par D u)/s u)^a.1 /s ⊥^n = (area D p₀ s (cove D U u)/s u^a.1)*(s (par D u)^a.1*area D p₀ s (univ\cove D U u) /s ⊥^n):=by
   rw [area_volume D u,div_pow]; ring -- hu/hp unused
variable (A:Allot C)(hL:Lanes (F:=Λ) T.sector.derivatives)(h:Services C Λ S)
   {φ:Filter I}{x:I→X→ℝ}{r:I→ℝ}{η M c:ℝ} (Y:Burst D U φ r x)
omit hp hu
-- revision limits preserved when trim
include Y
lemma Burst.heal {Q:Finset X}(hf:Q ⊆ U)(hq:Crown Q) : Burst D Q φ r x:=by
    refine ⟨fun η hη=>?_,Y.fronts.mono fun _ h i hi=> h i (hf hi)⟩; let p:=Y.fresh η hη; exact ⟨hq,p.ray,hη,fun v hv=>p.fade v (hf hv),fun v hv=>p.charge v (hf hv),p.dim.mono fun _ h v hv=> h v (hf hv)⟩
omit Y in
lemma Ridge.heals {K':Finset X}(h:K'⊆U)(x:X→E4)(hh:Ridge s η M D U x): Ridge s η M D K' x:=by
    have hp:allUp D K' ⊆ allUp D U:= Finset.union_subset (h.trans subset_union_left) (brim_under D U K' h); exact ⟨hh.belly,fun x y hx hy hv=>hh.near x y (h hx) (hp hy) hv,fun x y hx hy hv hw=>hh.span _ _ (hp hx) (hp hy) hv hw⟩ -- K' notation conflicts
local notation "A!"=> fun (n:ℕ) (q:C.book.Token) (i:I)=> x i (par D u)^q.1*area D p₀ (x i) (univ\k)/ (x i ⊥)^n
variable (hP:P.Coherent) (z:I→ X→E4) (hη:0<η)(hM:0≤ M)
-- grants
include A hL hP h hp hu hη hM Y
lemma note_gains (a:Mode T.sector.derivatives) (t:C.book.Token) : ∃ f:I→ℝ,Score φ r f∧ ∀ᶠ i in φ,∀ z, Ridge (x i) η M D U z → A! a.fst t i *‖P.ope a (picked H z) (picked H (pallet p t u)) 0‖ ≤ f i:=by
    let K:=Arboreal.trim U u
    have he:K⊆ U:= Finset.filter_subset ..; obtain ⟨f,hf,hU⟩:=sturdy_coeff D T A h hL hP (picked H (pallet p t u)) (Burst.heal D Y he (remains _ hp ((rest_mem ..).mp hu|>.1))) hη hM a; refine ⟨f,hf,?_⟩; filter_upwards [hU] with i hi z hz; have hy:=hi _ (Ridge.heals D he _ hz); rw [← trimmed_units D p hp hu t]; apply le_trans (le_of_eq ?_) hy
    let Z:=‖P.ope a (picked H z) (picked H (pallet p t u)) 0‖; change (_ / _)*Z = Z*volume D K (p' t) (x i)/_; ring
variable [Fintype J'] (y:I→J'→E4)(q:J'→ C.book.Token)(v:I→ Viewers T)
lemma test_fee (t:C.book.Token)(n:ℕ)(hc:0<c)(hy:∀ᶠ i in φ, ClearOf 0 (y i) c): ∃ f:I→ℝ, Score φ r f ∧ ∀ᶠ i in φ,∀ z, Ridge (x i) η M D U z → A! n t i * ‖observe (spectator T (v i)) (beside (picked H z) (y i)) (beside (picked H (pallet p t u)) q) -P.truncated (spectator T (v i)) n (picked H z) (picked H (pallet p t u)) 0 (y i) q‖ ≤ f i:=by
    let K:=Arboreal.trim U u; let p₁:= picked H (pallet p t u); have he: K⊆ U:=filter_subset ..; have hp':=Burst.heal D Y he (remains _ hp ((rest_mem ..).mp hu|>.1)); obtain ⟨f,hf,hK⟩:= sturdy_test D T A h hL hP p₁ v y q hp' hη hM n hc hy; let H':=hp'.fresh η hη
    refine ⟨f,hf,?_⟩; let j i:=x i ⊥; have hh:= H'.fade _ H'.crowned.base; let V' i:= volume D K (p' t) (x i)
    filter_upwards [hh.eventually self_mem_nhdsWithin,(hh.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one),(H'.brim_paid D p₁),hK] with i hi hc he' hκ z hz
    let Z:=‖observe (spectator T (v i)) (beside (picked H z) (y i)) (beside p₁ q)-P.truncated (spectator T (v i)) n (picked H z) p₁ 0 (y i) q‖; have hz' := hκ z (Ridge.heals D he z hz)
    rw [← trimmed_units D p hp hu t]; change (V' i/_)*Z ≤ _; apply le_trans _ hz'; change _ ≤ Z*V' i/(j i)^(n+1); rw [mul_comm _ Z, ← mul_div_assoc]; exact div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (le_of_lt he')) (pow_pos hi _) (pow_le_pow_of_le_one (le_of_lt hi) hc n.le_succ)
end YM.OPE.Arboreal.Trace
