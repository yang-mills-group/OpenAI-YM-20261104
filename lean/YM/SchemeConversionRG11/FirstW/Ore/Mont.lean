import YM.SchemeConversionRG11.FirstW.Ore.Chunks
/-! seminorm charges and finite-dimensional bases with Level-zero storage. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11
open scoped BigOperators Classical ContDiff
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G} {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def Honey (f:ℕ→V): Prop:= ∃ C:ℝ,∀ᶠ i in atTop, ‖f i‖≤C
omit [NormedSpace ℝ V] in
lemma Smoke {f g:ℕ→ V} (h:Honey f)(he:Honey g):Honey (fun i=> f i+g i):=by
 obtain ⟨C,h⟩:=h;obtain ⟨D,p⟩:=he; exact ⟨C+D,(h.and p).mono fun i hi=> le_trans (norm_add_le ..) (add_le_add hi.1 hi.2)⟩ -- omit V NormedSpace
lemma Honey.sink {f:ℕ→V}{g:ℕ→ℝ}(h : Honey f)(p:Tendsto g atTop (𝓝 0)): Tendsto (fun i=>g i • f i) atTop (𝓝 0) := by
 obtain ⟨C,H⟩:=h; rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (H.mono fun i hi=>show _≤ ‖g i‖ *C from ?_) (by simpa only [norm_zero,zero_mul] using p.norm.mul_const C)
 rw [norm_smul]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
omit [NormedSpace ℝ V] in
lemma Honey.helen {f:ℕ→V}(h:Helen f): Honey f:=by obtain ⟨x,h⟩:= h; exact ⟨_,h.norm.eventually (ge_mem_nhds (lt_add_one _))⟩
lemma closeHold {a b:ℤ}{f:ℕ→V}(h:a≤b)(hp:Helen (fun i=> T.gap i ^ a • f i)) : Helen (fun i=> T.gap i ^ b • f i):=by
 obtain ⟨d,hd⟩ : ∃ d:ℕ,b=(d:ℤ)+a:= ⟨(b-a).toNat,by omega⟩; obtain ⟨x,hx⟩:=hp
 exact ⟨_,((T.cutoff.pow d).smul hx).congr fun i=>by rw [hd,smul_smul,zpow_add₀ (T.positive i).ne',zpow_natCast]⟩
lemma honey_handles (p:ℕ→Field4 G) (hp:∀ i:Edge Cover,Honey (fun j=>p j i)) (x:Finset (Edge Cover)): Honey (fun i=> (fun v:↥x => p i v.val)):=by
 choose C h using fun v:↥x=>hp v.val; let K:=1+∑ v:↥x,|C v|
 have hK:0<K:=add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun _ _=>abs_nonneg _)
 refine ⟨K,(eventually_all.mpr h).mono fun i hi=>?_⟩
 refine pi_norm_le_iff_of_nonneg hK.le|>.2 fun v=>(hi v).trans ?_
 exact (le_abs_self _).trans ((Finset.single_le_sum (f:=fun v:↥x=>|C v|) (fun _ _=>abs_nonneg _) (Finset.mem_univ v)).trans (by unfold K; linarith))
lemma Honey.tint (T:Itinerary)(a:Who G 6)(x:Edge Cover): Honey (fun i=>pit T a i x):=by
 obtain ⟨C,hc,H⟩:=(wheel_live T a 1).1 x.2; let X:= C * stepY x.1 ^ (-((fee a+1:ℕ):ℤ)); refine ⟨X,?_⟩
 filter_upwards [H, Tendsto.norm (inc_const T x.1)|>.eventually (ge_mem_nhds (show ‖(0:E4)‖<1 by simp))] with i hi h
 have hp := hi x.1 (show Jam T 1 i x.1 from h); simpa only [pit,X,zpow_zero,mul_one] using hp
lemma stayB (A B:ℕ→Field4 G)(x : Labels.Key G)(h : ∀ i:Edge Cover,Honey (fun j=> A j i))(hp : ∀ i:Edge Cover,Honey (fun j=> B j i)): Honey (fun j=> echoAt 0 x (A j) (B j)) := by
 obtain ⟨S,H⟩:= finite_glow x
 let f (A:ℕ →Field4 G) (j:ℕ) (v:↥S):= A j v.val
 obtain ⟨C,hC⟩:=honey_handles _ h S; obtain ⟨D,hD⟩:= honey_handles _ hp S
 obtain ⟨L,hL⟩:= doubles (((echoAt (0:Cover) x).compl₂ (cle G S)).comp (cle G S)); refine ⟨‖L‖*C*D,?_⟩
 filter_upwards [hC,hD] with i hi hj
 have he (A:ℕ→Field4 G) : EqOn (cle G S (f A i)) (A i) ↑S := fun v hv=> by dsimp only [cle,LinearMap.coe_mk,AddHom.coe_mk, clearWind]; rw [dif_pos (show v∈S from hv)]
 have ht: L (f A i) (f B i) = echoAt 0 x (A i) (B i):= by rw [hL,LinearMap.comp_apply, LinearMap.compl₂_apply,H _ _ _ _ (he A) (he B)]
 rw [←ht]; exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))) hj (norm_nonneg _) (mul_nonneg (norm_nonneg L) ((norm_nonneg (f A i)).trans hi)))
-- finite dependencies of native read. synth support by linear response core eval
private lemma actualCap (k:Labels.Key G)(v:Cover): ∃ s:Finset (Edge Cover),∀ A B:Field4 G, EqOn A B s → native k v A=native k v B:=by
 have he (t:Signed)(p:Cover)(i:Axis): ∃ s:Finset (Edge Cover),∀ A B:Field4 G,EqOn A B s → Bare.wideLink G t A (p,i)=Bare.wideLink G t B (p,i) := by
    let q:= ((posDir i).rotate t).used (t.act p); exact ⟨{q},fun A B h=>by simp only [Bare.wideLink_apply]; rw [show _=_ from h (x:=q) (Finset.mem_singleton_self _)]⟩
 have hp(t:Signed)(p:Cover)(i j:Axis):∃ s:Finset (Edge Cover),∀ A B:Field4 G,EqOn A B s → Bare.wideCurl (Bare.wideLink G t A) p i j = Bare.wideCurl (Bare.wideLink G t B) p i j:=by
    obtain ⟨a,H⟩:=he t p i; obtain ⟨b,ht⟩:=he t (p+step i) j; obtain ⟨w,hq⟩:=he t (p+step j) i; obtain ⟨d,x⟩:=he t p j; refine ⟨(a∪b)∪(w∪d),fun A B h=>?_⟩; simp only [Finset.coe_union,Set.eqOn_union] at h; unfold Bare.wideCurl; rw [H _ _ h.1.1,ht _ _ h.1.2,hq _ _ h.2.1,x _ _ h.2.2]
 let c(t:Signed):= affine t⁻¹ 0 v
 let I:= Signed × Axis × Axis × (Fin k.1→Axis) × Finset (Fin k.1)
 choose S hS using fun (t:Signed) i j (w:Fin k.1→Axis) (s:Finset (Fin k.1))=> hp t (c t+∑ i∈s,step (w i)) i j
 let U:=Finset.univ.biUnion (fun x:I=> S x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
 refine ⟨U,fun A B h=>?_⟩
 have hv (t:Signed): Bare.wideCore G k.1 (c t) (Bare.wideLink G t A)=Bare.wideCore G k.1 (c t) (Bare.wideLink G t B):=by
    funext i j x; simp only [Bare.wideCore_apply]; apply congrArg _; apply Finset.sum_congr rfl; intro d _; have hp:S t i j x d⊆U:=fun a ha=> Finset.mem_biUnion.mpr ⟨(⟨t,i,j,x,d⟩: I),Finset.mem_univ _,ha⟩
    rw [hS t i j x d A B (h.mono (Finset.coe_subset.mpr hp))]
 unfold c at hv; simp only [native,tape, LinearMap.comp_apply,Bare.wideLinear,LinearMap.sum_apply, LinearMap.smul_apply,hv]
lemma footprint (p:ℕ→Field4 G) (x:Labels.Key G)(h:∀ i: Edge Cover,Honey (fun j=> p j i)): Honey (fun j=>native x (0:Cover) (p j)) := by
 obtain ⟨S,H⟩:= actualCap x 0
 let f (j:ℕ)(v:↥S):= p j v.val; obtain ⟨C,hc⟩ := (show Honey f from honey_handles p h S)
 let L:= (native x (0:Cover) ∘ₗ cle G S).toContinuousLinearMap; have ht (i:ℕ): native x (0:Cover) (p i)= L (f i):=by
   rw [show L (f i)=native x (0:Cover) (cle G S (f i)) from rfl]; apply H; intro j hj; simp only [cle,LinearMap.coe_mk,AddHom.coe_mk, clearWind,dif_pos (show j∈S from hj)]; rfl
 refine ⟨‖L‖*C,hc.mono fun i hi=>?_⟩; change ‖native x (0:Cover) (p i)‖ ≤ _; rw [ht]; exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg L))
end YM.RG11.FirstW
