import YM.SchemeConversionRG11.FirstW.Lien.Mains
/-! Paid correction maps and restriction types on weights/gradient. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G:Gauge} {F : Labels.Frames G}
set_option synthInstance.maxHeartbeats 90000 in
instance honduras : AddCommGroup (Bond F) := by exact @Submodule.addCommGroup ℝ (Letter G F) _ _ _ (bath F)
instance BondDim : FiniteDimensional ℝ (Bond F) := by
 haveI f₁ : Module.Free ℝ (la G) := @Module.Free.of_divisionRing ℝ _ _ _ _
 haveI f₂: Module.Free ℂ (E F 6):= @Module.Free.of_divisionRing ℂ _ _ _ _
 haveI hp: Module.Finite ℝ (la G →ₗ[ℝ] ℂ) := Module.Finite.linearMap ℝ ℝ _ _
 haveI hD : Module.Finite ℝ (Rhythm G):= Module.Finite.linearMap ℝ ℝ _ _
 haveI hv : Module.Finite ℝ (Letter G F) := Module.Finite.linearMap ℂ ℝ _ _
 exact @FiniteDimensional.of_injective ℝ (Bond F) _ _ _ (Letter G F) _ _ (bath F).subtype Subtype.val_injective hv -- order check
def tuningC (F:Labels.Frames G) (p : Hex F): Rhythm G:= (poem ⟨Full.sections 6 F p.val,p.property⟩).choose
lemma tuning_eq (F:Labels.Frames G)(p:Hex F)(x y:la G): tuningC F p x y= chord x.val y.val (Full.sections 6 F p.val) := by
 have h:= (poem ⟨Full.sections 6 F p.val,p.property⟩).choose_spec x y; exact h
lemma chord_tint (u : G.El) (x y:la G)(p:E F 6) : chord x.val y.val (Full.sections 6 F p)= chord (ColorS u 4 x).val (ColorS u 4 y).val (Full.sections 6 F p) := by
 have ht (A:Field4 G): sun (putting u A) (Full.sections 6 F p)=sun A (Full.sections 6 F p) := by
   unfold sun; rw [show stageW G (putting u A)= Labels.colored u (stageW G A) from funext fun l=> letter_key A u 0 l 1]; exact (physicalLabel F 6 p).property.2 ..
 simp only [chord_at,ColorS,←map_add (f:=putting u),ht] -- simp args
lemma suitsP (q:Pack F): SuitedP q.val:= q.property
def glyph0 (q:Pack F): Letter G F where
 toFun p:= tuningC F (⟨q.val p,(suitsP q).sees p⟩)
 map_add' p w:= by apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; simp only [LinearMap.add_apply,tuning_eq,map_add]
 map_smul' c p:= by apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; simp only [LinearMap.smul_apply,tuning_eq,RingHom.id_apply,map_smul]
lemma glyph0_eq (q : Pack F) (p:E F 6)(x y:la G): glyph0 q p x y= chord x.val y.val (Full.sections 6 F (q.val p)):= tuning_eq _ _ _ _
def glyph1 (q : Pack F): Bond F:= ⟨glyph0 q, by
 refine ⟨fun p hp=>?_,fun p x y=>?_,fun u p x y=>?_,fun p x y=>?_,fun s p x y=>?_⟩
 · apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; rw [glyph0_eq,(suitsP q).sunk _ hp,map_zero,map_zero];rfl
 · rw [glyph0_eq,glyph0_eq,chord_com]
 · rw [glyph0_eq,glyph0_eq]; exact (chord_tint u _ _ _).symm
 · rw [glyph0_eq,glyph0_eq,← (suitsP q).proofP p, trip_star F]
 have he (x:la G): Bare.wideLink G s x.val=(rink s x).val:=rfl
 rw [glyph0_eq,glyph0_eq,(suitsP q).torque,trip_test F,he,he]⟩
def glyph (F:Labels.Frames G) : Pack F →ₗ[ℝ] Bond F where
 toFun:=glyph1
 map_add' v w:=by apply Subtype.ext; apply LinearMap.ext; intro p; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; change glyph0 (v+w) p x y=glyph0 v p x y+glyph0 w p x y; simp only [glyph0_eq,Submodule.coe_add,LinearMap.add_apply,map_add]
 map_smul' c v:=by
   apply Subtype.ext; apply LinearMap.ext; intro p; apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
   change glyph0 (c • v) p x y=c • glyph0 v p x y
   rw [glyph0_eq,glyph0_eq,SetLike.val_smul, LinearMap.smul_apply]; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) c (v.val p), map_smul,Complex.real_smul];rfl -- wrong complex slot
lemma tune_eq (q:Pack F)(p:E F 6)(x y:la G): (glyph F q).val p x y= chord x.val y.val (Full.sections 6 F (q.val p)):= glyph0_eq q p x y
lemma song_dead (q:Pack F)(p:E F 6)(x y:la G)(h:quietly x.val): (glyph F q).val p x y=0 := by rw [tune_eq]; exact dead_note x h ⟨_,(suitsP q).sees p⟩ y.val
-- truncation submodules. model is exact in Net, linear lift kills Net complement
structure CheckQ (F:Labels.Frames G) where
 p:E F 6
 i:ℕ
 j:ℕ
 a:la G
 b:la G
 e:a.val∈cabin G i
 h:b.val∈cabin G j
def rate (q:CheckQ F): Bond F→ₗ[ℝ]ℂ where
 toFun B:=B.val q.p q.a q.b
 map_add' _ _ := rfl
 map_smul' _ _:= rfl
def mask (F:Labels.Frames G) (i:ℕ): Submodule ℝ (Bond F) where
 carrier:=setOf fun B=>∀q:CheckQ F,q.i+q.j < i → rate q B=0
 zero_mem':=fun _ _=> map_zero _
 add_mem' {a b} h p:=fun q e=> by rw [map_add,h q e,p q e,add_zero]
 smul_mem' c a h:=fun q e=>by rw [map_smul, h q e,smul_zero]
def hum (F:Labels.Frames G)(i:ℕ): Submodule ℝ (Bond F) where
 carrier:=setOf fun B=>∀ q:CheckQ F,q.i+q.j < i → quietly q.a.val → rate q B=0
 zero_mem':=fun _ _ _=>map_zero _
 add_mem' {a b} h p:=fun q e f=>by rw [map_add,h q e f,p q e f,add_zero]
 smul_mem' c a h:= fun q e f=>by rw [map_smul,h q e f,smul_zero]
lemma mask_more {i:ℕ} : mask F (i+1) ≤ mask F i⊓hum F (i+1) := fun _ hx=> ⟨fun q he=> hx q (he.trans (Nat.lt_succ_self i)),fun q he _=>hx q he⟩
lemma mask_precise (i:ℕ)(he:i≤4)(W:Bond F)(h:W∈mask F i⊓hum F (i+1)): ∃ q:Pack F, W-glyph F q∈mask F (i+1) := by
 have H:= willing i W he (fun p=> ⟨fun x y=>⟨(show TintD F W.val from W.property).fair p x y,fun a b hW ha hb e=>h.2 (⟨p,a,b,x,y,ha,hb⟩: CheckQ F) (Nat.lt_succ_of_le hW) e⟩,fun a b l j he ea eb=>h.1 ⟨p,l,j,a,b,ea,eb⟩ he⟩)
 obtain ⟨q,hq⟩:=H; refine ⟨q,fun s e=>?_⟩; rw [map_sub]; apply sub_eq_zero.mpr; change W.val s.p _ _=(glyph _ _).val s.p _ _; rw [tune_eq,hq s.p s.i s.j (Nat.lt_succ_iff.mp e) s.a s.b s.e s.h]
end YM.RG11.FirstW
