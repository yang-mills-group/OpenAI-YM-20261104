import YM.Pert.Scale.Engineering
import YM.RG12.Canonical.Basis
/-!
# True free echelons

Staying in exact H-oriented free comparator quotient; bases at distinct horizons must agree wrt
rises and grading, not just choose independent columns (nor conflate physical and Maxwell systems).
Use eigenspaces of length for compatible homogeneous choices (any section of full Wick-lifts would
also work).
-/
noncomputable section
namespace YM.RG12.Roof
open Function Set Filter Labels Table Maxwell Extra.FD OPE Pert.RawLabels Pert.Scale
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (F : Labels.Frames G) {d e j k : ℕ}
set_option quotPrecheck false
local notation "T!"=> freeTable F
local notation "P!"=> Free.scheme F
local notation "I!"=>Free.scheme_filters F
local notation:max "E!" d:max=> (freeTable F).Field d
lemma gear_rises (H : d ≤ e) (x : E! d) (t : ℝ) : gear F e t ((P!).rise H x) = (P!).rise H (gear F d t x):=by
    rw [gear_def,gear_def,physical_inclusion F (I!) H, enroll,enroll,UVNext.FreeStress.rise_embed F (P!) (I!)] -- expand enroll first rhs
    rfl

-- homogeneous column, own horizon. leading labels rather than an arbitrary complement.
def Peak(d:ℕ): Submodule ℂ (E! d) := LinearMap.ker (gear F d 2 - (((2:ℂ)^d) • (LinearMap.id:Module.End ℂ (E! d))))
variable (B:RStage F d)

lemma weighs_corner (i : Fin (B.m+1)) : ∃ j : (F.level d).Index, B.b i = enroll F d ((F.level d).basis j) ∧
    ((F.level d).grades j).1 = (B.w i).1 := by
   obtain ⟨j,hj⟩:= B.corners i
   have hx: pack F j = enroll F _ ((F.level d).basis j):= rfl
   refine ⟨j,hj.trans hx,?_⟩
   refine MvPolynomial.IsWeightedHomogeneous.inj_right (φ:=writes F d (B.b i)) ?_ ?_ (B.weighs i) -- port
   · exact fun he => B.b.ne_zero i ((writes_inj F d) (he.trans ((writes F d).map_zero.symm)))
   intro v hv; exact congrArg Prod.fst ((weight_collapse v).symm.trans (at_alcove F d j (hj ▸ hv)))
lemma enough_height (j:(F.level d).Index)(h:((F.level d).grades j).1 ≤ k) : ((F.level d).basis j : Label G d).val ∈ localFields G k:=by
   let A:=((F.level d).basis j : Label G d)
   refine ⟨?_,A.property.2⟩
   change A.val ∈ limited _ _; rw [limited,MvPolynomial.mem_restrictSupport_iff]; intro v hv
   change height v ≤ k
   apply le_trans _ h
   have hi := (pure_grade _ _).mp ((F.level d).pure j) (MvPolynomial.mem_support_iff.mp hv)
   exact (congr_arg Prod.fst ((weight_slot v).symm.trans hi)).le
lemma past (i : Fin (B.m+1)) (h : (B.w i).1 < d): B.b i ∈ old (P!) d := by
   obtain ⟨j,hj,hi⟩:= weighs_corner F B i
   cases d
   · exact (Nat.not_lt_zero _ h).elim
   rename_i d
   let Q:= (F.level (d+1)).basis j
   refine ⟨UVNext.FreeStress.embed F d ⟨Q.val,enough_height F j (hi.trans_le (Nat.le_of_lt_succ h))⟩,?_⟩
   rw [hj]
   apply UVNext.FreeStress.rise_embed F (P!) (I!) (.step (Nat.le_refl _)) _

lemma high_basis (i : Fin (B.m+1))(h:(B.w i).1 = d): B.b i∈Peak F d:=by
  change (gear F d 2) (B.b i)- ((2:ℂ)^d) • (B.b i)=0
  rw [rare,h]; simp
lemma price_coord (i : Fin (B.m+1))(x:E! d)(t:ℝ): (B.b.coord i) (gear F d t x)= (t:ℂ)^(B.w i).1 * B.b.coord i x:=by
    conv_lhs => rw [← B.b.sum_repr x, map_sum,map_sum]
    simp_rw [map_smul,Pert.Scale.rare,map_smul]
    rw [Finset.sum_eq_single i]
    · simp
      ring
    · intro j _ h; simp [h]
    simp
private lemma powders {i j:ℕ}(c : ℂ)(h:i≠j)(he: (2:ℂ)^i*c=2^j*c):c=0:=by
   by_contra! hc; apply h
   have hh := mul_right_cancel₀ hc he
   have h': (2:ℝ)^i=2^j:=by exact_mod_cast hh
   exact (pow_right_injective₀ (by norm_num : (0:ℝ)<2) (by norm_num)) h' -- lookup
lemma dualize (i : Fin (B.m+1))(h:(B.w i).1 < d)(x:Peak F d): B.b.coord i x.val=0:=by
   have hp:= x.property
   change gear F d 2 (x:E! d)-((2:ℂ)^d) • x.val=0 at hp
   have hm:= price_coord F B i x.val 2
   rw [sub_eq_zero.mp hp, map_smul] at hm
   apply powders _ (ne_of_lt h); simpa only [Complex.ofReal_ofNat,smul_eq_mul] using hm.symm
lemma dual_past (i:Fin (B.m+1))(h:(B.w i).1=d) (x:old (P!) d): B.b.coord i x.val=0:=by
   cases d with
   | zero=> have hx : x.val∈ (⊥:Submodule ℂ (E! 0)):=x.property; rw [(Submodule.mem_bot ..).mp hx,map_zero]
   | succ d=>
     obtain ⟨v,hv⟩:= x.property
     let B':=recorded F d
     have he(j:Fin (B'.m+1)): B.b.coord i ((P!).rise (Nat.le_succ d) (B'.b j))=0:=by
        have ht:= price_coord F B i ((P!).rise (Nat.le_succ d) (B'.b j)) 2
        rw [gear_rises,rare,map_smul,map_smul,h] at ht
        apply powders (i:=(B'.w j).1) (j:=d+1) _ (Nat.ne_of_lt (Nat.lt_succ_of_le (B'.cap j)))
        simpa using ht
     rw [← hv,← B'.b.sum_repr v,map_sum,map_sum]; simp_rw [map_smul, he, smul_zero, Finset.sum_const_zero]
include B
lemma spreadPeak (x:Peak F d)(t:ℝ): gear F d t x.val=(t:ℂ)^d • x.val:=by
   rw [← B.b.sum_repr x.val, map_sum, Finset.smul_sum]; apply Finset.sum_congr rfl
   intro i _; rw [map_smul,rare,smul_comm (M:=ℂ) (B.b.repr _ i)]
   obtain he|he:=eq_or_lt_of_le (B.cap i)
   · rw [he]
   change _ • (B.b.coord i x.val • _)= _ • (B.b.coord i _ • _)
   rw [dualize F B i he x]; simp
lemma together : IsCompl (Peak F d) (old (P!) d):=by
   constructor
   · rw [disjoint_iff]; apply le_antisymm _ bot_le
     intro x hx
     rw [Submodule.mem_bot]
     apply B.b.repr.injective
     ext i; obtain he|he:= eq_or_lt_of_le (B.cap i)
     · simpa using dual_past F B i he (⟨x,hx.2⟩)
     simpa using dualize F B i he (⟨x,hx.1⟩)
   rw [codisjoint_iff]; apply le_top.antisymm; intro x _; rw [← B.b.sum_repr x]; apply Submodule.sum_mem
   intro j _; apply Submodule.smul_mem
   obtain he|he:=eq_or_lt_of_le (B.cap j)
   · exact (le_sup_left:Peak F d ≤ _ ) (high_basis F B j he)
   exact (le_sup_right:old (P!) d ≤ _ ) (past F B j he)
omit B
section fit
variable {L:Register G}(S:Table L)(P:DiffPlan S)(h:S.Symmetric)(u:S.RealSpin)(hu:Maxwell.Ranks S u)(hP:P.Inclusions S)
include hu h hP
lemma similar d : addition P d=addition (Free.scheme L.grid) d:=by
   obtain ⟨v,hv⟩:= hu; cases d with
   | zero=> obtain ⟨q,hq⟩:=hv 0; have he:=q.finrank_eq; unfold addition; have hp:= Submodule.finrank_quotient_add_finrank (old P 0); have ht:=Submodule.finrank_quotient_add_finrank (old (Free.scheme L.grid) 0); have ha : Module.finrank ℂ ↥(old P 0)=0:= finrank_bot _ _; have hA : Module.finrank ℂ ↥(old (Free.scheme L.grid) 0)=0:= finrank_bot _ _; simp_rw [ha,add_zero] at hp; simp_rw [hA,add_zero] at ht; exact hp.trans (he.trans ht.symm)
   | succ d=>
     obtain ⟨q,-⟩:=hv d; obtain ⟨r,-⟩:=hv (d+1)
     have he:=q.finrank_eq; have hg:=r.finrank_eq
     have hp:= Submodule.finrank_quotient_add_finrank (old P (d+1)); have ht:=Submodule.finrank_quotient_add_finrank (old (Free.scheme L.grid) (d+1))
     have hx:= LinearMap.finrank_range_of_inj (P.inject h hP (Nat.le_succ d)); have hi:= LinearMap.finrank_range_of_inj ((Free.scheme L.grid).inject (table_sym _) (Free.scheme_filters _) (Nat.le_succ d))
     change addition P _+_= _ at hp
     change addition _ _+_= _ at ht
     change Module.finrank ℂ ↥(old P (d+1)) = _ at hx
     change Module.finrank ℂ ↥(old (Free.scheme L.grid) (d+1))= Module.finrank ℂ ((freeTable L.grid).Field d) at hi
     change addition (Free.scheme L.grid) (d+1)+_ = Module.finrank ℂ ((freeTable L.grid).Field (d+1)) at ht
     omega

def beacon (h:S.Symmetric)(u:S.RealSpin)(hu:Maxwell.Ranks S u)(hP:P.Inclusions S) (d : ℕ) : (Qname P d → ℂ) ≃ₗ[ℂ] Peak L.grid d:=by
    have hp:=together L.grid (recorded L.grid d)
    refine LinearEquiv.ofFinrankEq _ _ ?_
    have he:=Submodule.finrank_add_eq_of_isCompl hp
    have hr:= Submodule.finrank_quotient_add_finrank (old (Free.scheme L.grid) d)
    change addition (Free.scheme L.grid) _ + Module.finrank ℂ _ = Module.finrank ℂ ((freeTable L.grid).Field d) at hr
    -- p vars not included (def binders)
    rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,similar S P h u hu hP]
    change Module.finrank ℂ ↥(Peak L.grid d)+Module.finrank ℂ ↥(old (Free.scheme L.grid) d) = Module.finrank ℂ ((freeTable L.grid).Field d) at he
    change addition (Free.scheme L.grid) d+Module.finrank ℂ ↥(old (Free.scheme L.grid) d) = _ at hr
    omega
end fit
section tower
set_option maxHeartbeats 660000
-- Direct physical-basis requirement in subsequent consumers. C dependence only in choosing free dims.
variable {C:Family G}{S:Table C.book}(P:DiffPlan S)(h:S.Symmetric)(u:S.RealSpin)(hu: Ranks S u)(hP:P.Inclusions S)
def lane (C : Family G) (S:Table C.book) (P : DiffPlan S)(j d:ℕ) (m:j≤d) (h:S.Symmetric)(u:S.RealSpin)(hu: Ranks S u)(hP:P.Inclusions S): (Qname P j→ℂ)→ₗ[ℂ] (freeTable C.labels).Field d := (Free.scheme C.labels).rise m ∘ₗ ((Peak C.labels j).subtype ∘ₗ (beacon S P h u hu hP j).toLinearMap)
set_option quotPrecheck false
local notation "lanes"=> lane C S P _ _
local notation "F!"=>freeTable C.labels
-- across k grades
include u h hu hP
lemma gauged (t:j≤d)(x:Qname P j→ℂ)(s:ℝ) : gear C.labels d s (lanes t h u hu hP x)=(s:ℂ)^j • lanes t h u hu hP x:=by
   unfold lane; simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,gear_rises,spreadPeak C.labels (recorded C.labels j),map_smul]
def rigid (d : ℕ)(h:S.Symmetric)(u:S.RealSpin)(hu:Ranks S u)(hP:P.Inclusions S):RG12.Frames.Col (Desk.Sector P d)→ₗ[ℂ] (F!).Field d:=
    ∑ i:RG12.Frames.Grade d,((lanes i.is_le h u hu hP).comp (LinearMap.proj i))
lemma rigid_block d (i:RG12.Frames.Grade d)(x:Qname P i→ℂ) : rigid P d h u hu hP (RG12.Frames.put _ i x)=lane _ _ _ _ _ i.is_le h u hu hP x:=by
   simp only [rigid,LinearMap.sum_apply, LinearMap.comp_apply]
   rw [Finset.sum_eq_single i]
   · simp [RG12.Frames.put]
   · intro j _ hj
     simp [RG12.Frames.put,Pi.single_eq_of_ne hj]
   simp
open Finset RG12.Frames
private lemma gear_full (d:ℕ) : Function.Surjective (rigid P d h u hu hP):=by
   induction d with
   | zero=>
     intro y
     obtain ⟨p₁,p₂,he⟩:= Submodule.existsUnique_add_of_isCompl (together _ (recorded C.labels 0)) y -- `_`
     obtain ⟨x,rfl⟩:=(beacon S P h u hu hP 0).surjective p₁
     have hx:p₂.val=0:= (Submodule.mem_bot ..).mp (show p₂.val∈(⊥:Submodule ℂ ((F!).Field 0)) from p₂.property)
     rw [hx,add_zero] at he
     refine ⟨put _ (Fin.last 0) x,?_⟩
     rw [rigid_block]
     change (Free.scheme C.labels).rise (Nat.le_refl 0) _ = y
     rw [(Free.scheme C.labels).arrival (table_sym _) (Free.scheme_filters _)]
     exact he.1
   | succ d ih=>
     intro y
     obtain ⟨p₁,p₂,he,-⟩:= Submodule.existsUnique_add_of_isCompl (together _ (recorded C.labels (d+1))) y
     obtain ⟨x,rfl⟩:=(beacon S P h u hu hP (d+1)).surjective p₁
     obtain ⟨q,hq⟩:=p₂.property
     obtain ⟨v,hv⟩:= ih q
     exact ⟨put _ (Fin.last (d+1)) x + ∑ i:RG12.Frames.Grade d,put _ (Fin.castSucc i) (v i), by
       rw [map_add,map_sum, rigid_block]; simp_rw [rigid_block]
       change (Free.scheme C.labels).rise (Nat.le_refl (d+1)) ((beacon S P h u hu hP (d+1)) x).val + ∑ i:RG12.Frames.Grade d,(Free.scheme C.labels).rise (i.is_le.trans (Nat.le_succ d)) ((beacon S P h u hu hP i.val) (v i)).val = y
       rw [(Free.scheme C.labels).arrival (table_sym _) (Free.scheme_filters _),← he,← hq,← hv] -- lemma expansion input?
       rw [rigid,LinearMap.sum_apply,map_sum]
       simp_rw [LinearMap.comp_apply, lane,LinearMap.comp_apply]
       simp_rw [(Free.scheme C.labels).transit (table_sym _) (Free.scheme_filters _)]
       rfl⟩
lemma beam {Q:Prescription P}(hQ:Q.Coherent)(d:ℕ) : ∃ b:RG12.Frames.Col (Desk.Sector P d)≃ₗ[ℂ] (F!).Field d, ∀ (i:RG12.Frames.Grade d)(x:Qname P i→ℂ), b (put _ i x)=lanes i.is_le h u hu hP x:=by
    let E:= Desk.official Q hQ d
    have hi : Function.Bijective (rigid P d h u hu hP):=by
       have hG := gear_full P h u hu hP d
       obtain ⟨a,ha⟩:= hu;obtain ⟨b,hb⟩:=ha d
       exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ((E.trans b).finrank_eq)).mpr hG,hG⟩
    exact ⟨LinearEquiv.ofBijective _ hi, by intro i x; exact rigid_block P h u hu hP d i x⟩
end tower
end YM.RG12.Roof
