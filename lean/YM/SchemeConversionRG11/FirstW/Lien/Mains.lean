import YM.SchemeConversionRG11.FirstW.Lien.Reel
/-! This realizes the actual field-array CT matrices, ordering star and rotations. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G : Gauge} {F : Labels.Frames G} {k : ℕ}
def slips (B:PlayerM F) := ∀ p,B p∈Hex F
def sunkP (B:PlayerM F) := ∀ p,sink p → B p=0
def trueP (B:PlayerM F):= ∀ p:E F 6,bar F 6 (B p)=B (bar F 6 p)
def spinsP (B:PlayerM F):= ∀ s:Signed,∀ p:E F 6,B (tripS F s p)=tripS F s (B p)
def glass (B:PlayerM F) : PlayerM F where
 toFun p:=bar F 6 (B (bar F 6 p))
 map_add' p q:=by simp
 map_smul' a p:=by simp
abbrev temper (B:PlayerM F): PlayerM F := (2:ℂ)⁻¹ • (B+glass B)
lemma qualifies {B:PlayerM F} (h:slips B)(hk:sunkP B){W:Bond F}(hr:CompR W k B): slips (temper B) ∧ sunkP (temper B) ∧ CompR W k (temper B) ∧ trueP (temper B) := by
 have hs (p:E F 6): temper B p = (2:ℂ)⁻¹ • (B p+bar F 6 (B (bar F 6 p))) := rfl
 refine ⟨fun p=>?_,fun p he=>?_,fun p i j ij x y hx hy=>?_,fun p=>?_⟩
 · rw [hs]; exact Submodule.smul_mem _ _ (Submodule.add_mem _ (h p) (trip_B F _ (h _)))
 · rw [hs,hk p he,hk _ (sink_bar he),map_zero, add_zero,smul_zero]
 · have hc (u:E F 6) := hr u i j ij x y hx hy
   rw [hs,map_smul,map_add,map_smul,map_add,trip_star,hc p,hc (bar F 6 p),(show TintD F W.val from W.property).realP,star_star]; simp [← two_smul ℂ]
 rw [hs,map_smulₛₗ,hs,map_add]; simp only [bar, Table.reflect_star, map_inv₀,map_ofNat]; rw [add_comm]
def party (s:Signed)(B:PlayerM F) := tripS F s ∘ₗ (B ∘ₗ tripS F s⁻¹)
lemma horning (s:Signed){B:PlayerM F}(hp:slips B)(ht:sunkP B){W: Bond F}(hr:CompR W k B)(he:trueP B): slips (party s B) ∧ sunkP (party s B) ∧ CompR W k (party s B) ∧ trueP (party s B) := by
 have hs (p:E F 6) : party s B p= tripS F s (B (tripS F s⁻¹ p)) := rfl
 refine ⟨fun p=> by rw [hs]; exact trip_H F s (hp _), fun p hx=>by rw [hs,ht _ (trip_s _ _ _ hx),map_zero],fun p i j ij x y hx hy=>?_,fun p=>?_⟩
 · rw [hs,trip_test]
   let A:=rink s x; let t:=rink s y; have hy1 : A.val∈ cabin G i:=track_cabin s _ hx; have ht1 : t.val∈cabin G j:=track_cabin s _ hy
   have e (x:la G): Bare.wideLink G s x.val=(rink s x).val:=rfl
   have hw : chord A.val t.val (Full.sections 6 F (B (tripS F s⁻¹ p)))=W.val (tripS F s⁻¹ p) A t := hr (tripS F s⁻¹ p) i j ij A t hy1 ht1
   unfold A t at hw
   rw [e,e,hw, ←(show TintD F W.val from W.property).rotP,trip_p,mul_inv_cancel,trip_i]
 rw [hs,hs,trip_b,he,trip_b]
def stampP (B: PlayerM F) : PlayerM F:= (Fintype.card Signed:ℂ)⁻¹ • ∑ i:Signed,party i B
lemma stampU (B:PlayerM F)(p:E F 6) : stampP B p =(Fintype.card Signed:ℂ)⁻¹ • ∑ i:Signed,party i B p := by simp [stampP]
lemma uplift {B:PlayerM F}(hp:slips B)(ht:sunkP B){W: Bond F}(hr: CompR W k B)(he:trueP B) : slips (stampP B) ∧ sunkP (stampP B) ∧ CompR W k (stampP B) ∧ trueP (stampP B) ∧ spinsP (stampP B) := by
 have e s:= horning s hp ht hr he
 have h : (Fintype.card Signed:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
 refine ⟨fun p=>?_,fun p hx=>?_,fun p i j ij x y hx hy=>?_,fun p=>?_,fun s p=>?_⟩
 · rw [stampU]; exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=> (e i).1 p)
 · rw [stampU,Finset.sum_eq_zero,smul_zero]; exact fun i _=> (e i).2.1 p hx
 · have hx(s : Signed) := (e s).2.2.1 p i j ij x y hx hy
   rw [stampU,map_smul,map_smul,map_sum,map_sum]; simp_rw [hx]; rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,inv_smul_smul₀ h]
 · rw [stampU,map_smulₛₗ,map_inv₀, map_natCast,map_sum,stampU]; exact congrArg _ (Finset.sum_congr rfl fun i _=> (e i).2.2.2 p)
 rw [stampU,stampU,map_smul,map_sum]; apply congrArg _; rw [← Equiv.sum_comp (Equiv.mulLeft s) (fun i=> party i B (tripS F s p))]; apply Finset.sum_congr rfl; intro a _; change tripS F (s*a) (B (tripS _ _ _))=_; unfold party; simp only [LinearMap.comp_apply,trip_p]; simp [mul_assoc]
-- spaces actual increments with C-linear Qu, submodule real
structure SuitedP (B: PlayerM F): Prop where
 sees: slips B
 sunk: sunkP B
 proofP:trueP B
 torque:spinsP B
def tailored (F : Labels.Frames G): Submodule ℝ (PlayerM F) where
 carrier:=setOf SuitedP
 add_mem' {a b} ha hb:=by
    change SuitedP a at ha; change SuitedP b at hb
    refine ⟨fun p=>?_,fun p hp=>?_,fun p=>?_,fun s p=>?_⟩
    · rw [LinearMap.add_apply]; exact Submodule.add_mem _ (ha.sees _) (hb.sees _)
    · rw [LinearMap.add_apply,ha.sunk p hp,hb.sunk p hp,add_zero]
    · rw [LinearMap.add_apply,map_add,LinearMap.add_apply,ha.proofP,hb.proofP]
    rw [LinearMap.add_apply,ha.torque,hb.torque,LinearMap.add_apply,map_add]
 smul_mem' c a h:=by
    change SuitedP a at h
    have eh (v : E F 6) : ((c:ℝ) • a) v = (c:ℂ) • a v := RCLike.real_smul_eq_coe_smul (K:=ℂ) c _
    refine ⟨fun p=>?_,fun p hp=>?_,fun p=>?_,fun s p=>?_⟩
    · rw [eh]; exact Submodule.smul_mem _ _ (h.sees p)
    · rw [eh,h.sunk p hp,smul_zero]
    · rw [eh,eh,map_smulₛₗ,h.proofP]; simp
    rw [eh,h.torque,eh,map_smul]
 zero_mem':=⟨fun _=>Submodule.zero_mem _,fun _ _=>rfl,fun _=>map_zero _,fun _ _=>(map_zero _).symm⟩
abbrev Pack (F : Labels.Frames G):= ↥(tailored F)
def Outfit (Q : Pack F) : Buffer F 6:= ⟨(Q.val.restrictScalars ℝ).toContinuousLinearMap, by
  have h:SuitedP Q.val:= Q.property
  refine ⟨?_,fun i hi p hp=>?_,fun p=>h.proofP p,fun s p=>(h.torque s p).symm,fun p=>Q.val.map_smul _ p⟩
  · apply h.sunk; rw [sink, ←incl_range F (by decide: (5:ℕ)≤6)]; exact ⟨_,incl_unit F _⟩
  change Q.val p∈_; rw [h.sunk _ (sink_zero _ hi hp)]; exact Submodule.zero_mem _⟩
-- sym interpolants exist in this actual packed realization
lemma willing (n : ℕ) (W:Bond F) (hk:n≤4) (hp:Quieten F n W): ∃ q : Pack F,CompR W n q.val:= by
 obtain ⟨B,H,hs,hr⟩:=ontoQ F W n hk hp
 obtain ⟨hd,he,hj,ht⟩:=qualifies H hs hr
 obtain ⟨he,hE,hk,hq,hB⟩:= uplift hd he hj ht
 exact ⟨⟨_,he,hE,hq,hB⟩,hk⟩
end YM.RG11.FirstW
