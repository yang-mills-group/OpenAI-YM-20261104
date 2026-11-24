import YM.SignedWilsonExpansion.Grid.House
namespace YM.SignedWilsonExpansion.Overlap.Mirror
/-! # All pixels diagonal projection & stabilization by actual low-horizon basis. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open WickFace PhaseTilt Contrast AxialBill Scale Scale.Equator PairWave Marque
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}
local notation "E" => Module.End ℂ (Sec G 4)
local notation "ξ" => Normalize.leaf G 4
local notation "N" => Fintype.card G.ColorIndex
abbrev sl (G:Gauge)(u:Idx):= glow G u u
local notation "L" => sl G
local notation "W" => Sec G 4
def site : Stage 2:= ⟨ pairPoints (0:E4) (basis 3), pair_ok (Ne.symm (fun h=> by have ht:=basis_norm (3:Axis); rw [h,norm_zero] at ht; norm_num at ht )) ⟩
local notation "S" => site
lemma serves : Holds site:= by intro i; fin_cases i; exacts [ ⟨ (0:ℝ), (zero_smul ℝ _).symm⟩,⟨ (1:ℝ), (one_smul ℝ _).symm⟩ ]
abbrev amount (G:Gauge):= iris site (dd G)
local notation "K" => amount G
variable (h:G.Simple)
include h
lemma cost_ne: amount G≠0:= by intro he; unfold amount at he; have hp:= AxialBill.ep_pos h site serves; rw [he, Complex.zero_re] at hp; exact lt_irrefl _ hp
omit h
def revive (a:Axis): E:= ((2:ℂ)⁻¹) • ( (1:Module.End ℂ W) + ori (Signed.mirror a).ortho 4)
lemma glow_m (a:Axis)(u v:Idx) : ori (Signed.mirror a).ortho 4 (glow G u v)= if Normalize.mark u v a then -glow G u v else glow G u v:= by apply Subtype.ext; split_ifs with H; exacts [(Normalize.turn_label a u v).trans (if_pos H), (Normalize.turn_label a u v).trans (if_neg H)]
lemma sl_m (a:Axis)(u:Idx): ori (Signed.mirror a).ortho 4 ( sl G u )= sl G u:= by rw [sl, glow_m, if_neg (by simp [Normalize.mark] ) ]
lemma revive_on (a:Axis){z:W}(he:ori (Signed.mirror a).ortho 4 z=z): revive a z=z:= by rw [ revive, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, he ]; module
lemma glow_v (a:Axis)(u v:Idx): revive a (glow G u v)=if Normalize.mark u v a then 0 else glow G u v:= by rw [revive,LinearMap.smul_apply,LinearMap.add_apply,Module.End.one_apply, glow_m ]; split_ifs <;> module
lemma glow_t (i j:Idx) (r:Fin 10)(hr: twin (table r) i j): ori (tperm r).ortho 4 (sl G i)= sl G j:= by
  apply Subtype.ext; change reflectPol (tperm r).ortho (Normalize.label G i i)=Normalize.label G j j; unfold Normalize.label; rw [orient_team]; have he : actFlavor (tperm r).ortho 0 (cell (Normalize.left i) (Normalize.right i))=cell (Normalize.left j) (Normalize.right j) ∨ actFlavor (tperm r).ortho 0 (cell (Normalize.left i) (Normalize.right i))= -cell (Normalize.left j) (Normalize.right j):=by
      rcases hr with q|q <;> simp [tilt_one,tilt,tperm,q,cell_skew (Normalize.right j) (Normalize.left j)]
  simp_rw [show ∀ (p q : Flavor 0), team G p q=duetL G 0 0 p q from fun _ _=>rfl ]; rcases he with hh|hh <;> simp [hh]
lemma axisY (s: Ortho) : ori s 4 (ξ)=ξ:= by apply Subtype.ext; exact (reflectPol s).map_one
abbrev projection (G:Gauge): Module.End ℂ ( Sec G 4 ):= revive 0 ∘ₗ revive 1 ∘ₗ revive 2 ∘ₗ revive 3
def seats (v:Idx) : W→ₗ[ℂ]ℂ:= (K)⁻¹ • ( dyad site 0 1 (wmark G v v) ∘ₗ (coeS 4) )
def words : W→ₗ[ℂ]ℂ:= oneOnly site 0 ∘ₗ (coeS 4)
include h
lemma fares (u i j:Idx): seats u (glow G i j)= ( exclusive i u * exclusive j u:ℝ ):= by
    unfold seats; rw [LinearMap.smul_apply,LinearMap.comp_apply,show coeS 4 (glow G i j)=wmark G i j from rfl,Marque.dyAt site 0 1 (by decide) serves ]; rw [ show ↑( ( N*2*pay site 0 1^2*( exclusive i u*exclusive j u ):ℝ ) :ℝ )=(K:ℂ)*↑(( exclusive i u* exclusive j u:ℝ )) from (by unfold amount; rw [ AxialBill.Epair site serves ]; push_cast; rfl ) ]; rw [smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (cost_ne h),one_mul ]
lemma dim (u i:Idx): seats u (sl G i)= if i=u then 1 else 0:= by rw [ sl, fares h ]; unfold exclusive; split_ifs <;> simp
omit h
lemma heel (u:Idx): seats u (Normalize.leaf G 4)=0:= by rw [seats,LinearMap.smul_apply,LinearMap.comp_apply,show coeS 4 (ξ)= (1:WickPol G) from rfl, dropI site _ _ _ (by decide), WickFace.single_off, smul_zero ]
lemma word1 : words (Normalize.leaf G 4)=1:= coinS site 0
lemma word2 (a d:Idx): words (glow G a d)=0:= single_off site 0 a d
lemma vote (p:W)(he:∀ a: Axis, ori (Signed.mirror a).ortho 4 p=p): projection G p=p:= by simp only [ projection,LinearMap.comp_apply,revive_on _ (he 0),revive_on _ (he 1),revive_on _ (he 2),revive_on _ (he 3) ]
lemma glow_proj (u v:Idx)(hh:u≠v): projection G (glow G u v)=0:= by
    have ht : Normalize.mark u v 0 ∨ Normalize.mark u v 1 ∨ Normalize.mark u v 2 ∨ Normalize.mark u v 3:= (by decide : ∀ u v,u≠v→Normalize.mark u v 0∨ Normalize.mark u v 1 ∨ Normalize.mark u v 2 ∨ Normalize.mark u v 3 ) u v hh
    unfold projection; simp only [ LinearMap.comp_apply, glow_v ]; repeat' first| split| (simp only [LinearMap.comp_apply, glow_v]; split)| solve| simp only [map_zero] | tauto
def filmed (G:Gauge): Module.End ℂ (Sec G 4):= (words).smulRight (Normalize.leaf G 4)+∑ u:Idx,(seats u).smulRight ( sl G u )
lemma filmed_on (p:W): filmed G p= words p • (ξ)+∑ u:Idx, seats u p • ( sl G u ):= by rw [filmed,LinearMap.add_apply,LinearMap.sum_apply]; rfl
include h
lemma decomp (p:W): projection G p= words p • (ξ)+∑ u:Idx,seats u p • (L u):= by
    rw [← filmed_on]; refine WickFace.at_low h ( projection G ) ( filmed G ) ?_ ?_ p
    · rw [filmed_on,vote _ (fun _=> axisY _),word1,one_smul]; simp_rw [heel,zero_smul,sum_const_zero]; rw [add_zero]
    intro u v; rw [filmed_on,word2,zero_smul,zero_add]; by_cases H:u=v; · subst v; rw [ vote (sl G u) (fun a=> sl_m a u), Finset.sum_eq_single_of_mem u (mem_univ _), dim h u u ]; simp; intro b _ hb; rw [ dim h b u, if_neg hb.symm,zero_smul ]
    rw [ glow_proj _ _ H ]; symm; apply Finset.sum_eq_zero; intro b _; rw [ fares h b u v ]; by_cases hb:u=b; · rw [ show exclusive v b =0 from if_neg (hb ▸  Ne.symm H ), mul_zero ]; simp
    rw [ show exclusive u b=0 from if_neg hb,zero_mul ]; simp
lemma orders (T:Module.End ℂ (Sec G 4))(he:T∈Normalize.Change G 4) (u:Idx): T (L u)= words ( T ( L u ) ) • ξ+∑ v:Idx,seats v ( T ( L u ) ) • (L v):= by refine Eq.trans (vote (T (L u)) (fun a=> (he.2.2.2 _ _).symm.trans (congr_arg T (sl_m a u)))).symm (decomp h _)
lemma trade (T:Module.End ℂ (Sec G 4))(he:T∈Normalize.Change G 4) (a b c d:Idx)(r:Fin 10)(hr:twin (table r) a b)(hs:twin (table r) c d): seats b (T (L d))= seats a (T (L c)):= by
    rw [ ← glow_t c d r hs,he.2.2.2 ]; let X:= seats (G:=G) b; let σ:= ori (G:=G) (tperm r).ortho 4; generalize hs0 : T (L c)=p; rw [ show X (σ p)= X ( σ ( words p • ξ+∑ u:Idx,seats u p • ( L u ) ) ) from ?_ ]; swap; · symm; rw [← hs0,← orders h T he c]
    change X (σ _)=_; rw [ map_add,map_sum,map_smul,map_add,map_sum,map_smul, axisY, heel, smul_zero,zero_add ]; rw [ Finset.sum_eq_single_of_mem a (mem_univ _), map_smul,map_smul, glow_t a b r hr, dim h b b,if_pos rfl ]; simp
    intro u _ hu; have hv:= (by decide : ∀ u r, ∃ v, twin (table r) u v ) u r; obtain ⟨v,hv⟩:=hv; have hb:v≠b:= by intro hh; exact hu ((by decide : ∀ r u v b,twin (table r) u b → twin (table r) v b → u=v) r u a b ( hh ▸ hv ) hr)
    rw [ map_smul,map_smul,glow_t u v r hv,dim h b v, if_neg hb, smul_zero ]
end
end YM.SignedWilsonExpansion.Overlap.Mirror
