import YM.RGLocalTaylor.Retain.Fort
/-!
# Affine remainder aperture - local quotes with Mordant registration
Use larger ηR for coreE than λ² for all other inputs. Actual point honors
threshold-j, powers in stencil. Expense buy in Decal next, including on the
same tour.Marks into shared E/K follow Menu request.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open Mayer goodK Post
namespace Fort

variable {M i :ℕ} {f₁ f₂ : glyph G f} {X : Cash W s μ L Q o C T (impulse R f₂ a)}
variable {e vJ uJ K θ α γ β Z r' d' ρ:ℝ}
   {Ξ : Utopia H j v d r C' χ}
   {N : Captain H j C' d v Y A b r B q n χ}
   {w w':ℕ→ℝ}
   (hh : dual H f₂ a w w') (ha:Awning H Ξ A b d' e uJ vJ k l)
set_option quotPrecheck false
local notation "κ" => Opacity.key S
local notation "χ!" => impulse R f₂ a
local notation "Ru" => R.activities.E
local notation "V'" => (χ!).activities.E
local notation "RuM" => mantle H f₁ M
local notation "U!" => physical H M

-- compute prices for *every* Head.M stuffed Marker-Reads with ghost budgets w'.
def garment (S:StepData c f) (w:ℕ→ℝ)(A:ℝ) := Function.extend (Opacity.key S) (fun i=> A*w i) 0
def Fiber (Ξ: Utopia H j v d r C' χ) (w : ℕ→ℝ)(A:ℝ): Head S→ℝ:= Ξ.fare + garment S w A
abbrev bead (θ : ℝ) (n:ℕ):=θ+n
abbrev patchPrice (s e : ℝ)(M:ℕ):=(M+4:ℝ)*s+ e*↑M -- θ unused remove

local notation "λ'" => Fiber Ξ (w+w') γ
local notation "θ'" => bead θ M
local notation "Cₑ" => patchPrice r vJ M -- remove θ
local notation "w₀" => (w+w')

variable (hT : Q.goal L s≤ K)(hK: Approved K θ j M) (hg:1 ≤ ρ)(hρ:ρ*Q.goal L s ≤ 1)
    (hγ : 1 ≤ γ)(hL:∀ i,(w i+w' i)*ρ≤1)

lemma atom_f {t o b :ℝ} (he:1≤ρ)(hb:0≤ b)(hv:t*ρ≤1)(ht:0≤t)(hs:t≤o)(n:ℕ) : b*t^(n+1) ≤ (ρ^(n+1))⁻¹*(b*ρ)*o:=by
   have h := pow_le_one₀ (mul_nonneg ht (zero_le_one.trans he)) hv (n:=n)
   have hF:=pow_pos (zero_lt_one.trans_le he) (n+1); rw [mul_assoc (_⁻¹),inv_mul_eq_div, le_div_iff₀ hF]; calc
    _ = b*t*((t*ρ)^n) *ρ :=by ring
    _ ≤ _ := le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (mul_nonneg hb ht) h) (zero_le_one.trans he)) ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hb) (zero_le_one.trans he)).trans_eq (mul_right_comm ..))
-- unused hp remove
lemma stitch (p:Head S)(x:Fin (M+1))(u:Insert T)(h: Fits H u (H.supportP p) j): Fits H (u.mapSmooth (fun t:ℝ=> t^(x.val+1)/(x.val+1).factorial)) (H.supportP p) j:= h.mapSmooth ((contDiff_id.pow _).div_const _)
include hK
lemma cap : 1≤ θ' := hK.nonneg.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
omit hK
include hh hγ
lemma fibre_price (Ξ:Utopia H j v d r C' χ) (i : Head S): Ξ.fare i ≤ Fiber Ξ w₀ γ i:= by
   apply le_add_of_nonneg_right; by_cases ht:i∈Set.range (Opacity.key S)
   · obtain ⟨i,rfl⟩:=ht; obtain ⟨hx,hy⟩:= mnonneg H i hh; unfold garment; rw [(lifts _).extend_apply]; exact mul_nonneg (zero_le_one.trans hγ) (add_nonneg hx hy)
   unfold garment; rw [extend_apply' _ _ _ ht]; rfl
lemma fibre_pos (Ξ:Utopia H j v d r C' χ) (i) : 0≤ Fiber Ξ (w+w') γ i:=(Ξ.fares i).trans (fibre_price hh hγ Ξ i) -- binder Ξ hygiene contradiction
omit hh hγ in
lemma boosted_e (Ξ:Utopia H j v d r C' χ)(i:ℕ): γ*w₀ i ≤ Fiber Ξ w₀ γ (κ i):= by unfold Fiber garment; simp only [Pi.add_apply, (lifts _).extend_apply]; exact le_add_of_nonneg_left (Ξ.fares _)

omit hh hγ
include ha -- even though some unused, omit later
lemma boosted_width (i:ℕ): stampFactor H (κ i) vJ ≥ 0 := stamp_nonneg ha.cSc -- omit hh hγ
lemma chassis : (M+4:ℝ)*r ≤ Cₑ:= le_add_of_nonneg_right (mul_nonneg ha.cSc (Nat.cast_nonneg _))
lemma reach_price : 1 ≤ Cₑ:= (one_le_mul_of_one_le_of_one_le (by linarith only [Nat.cast_nonneg (α:=ℝ) M]) Ξ.active).trans (chassis ha)
lemma booths {x:Fin (M+1)}(i:ℕ)(ht:x.val < M): ((x.val+1:ℕ):ℝ)*stampFactor H (κ i) vJ ≤ stampFactor H (κ i) Cₑ :=by
   have hv : vJ*M ≤ Cₑ:= le_add_of_nonneg_left (mul_nonneg (by linarith only [Nat.cast_nonneg (α:=ℝ) M] : (0:ℝ)≤M+4) (zero_le_one.trans Ξ.active))
   have hS : 0 ≤ spanW T R (radiusB s) Q.halo (κ i):= by simpa only [stampFactor, one_mul] using stamp_nonneg (H:=H) (i:=κ i) zero_le_one
   exact (Eq.le (mul_assoc _ _ _).symm).trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) ha.cSc).trans (le_trans (le_of_eq (mul_comm _ _)) hv)) hS)
include hh hγ ha hK hρ hT hg -- not hL
lemma authentic : Priced Ξ M λ' θ' ρ Cₑ A U! := by
   refine ⟨fun Y p hp V h=> Mayer.quote_fits ..,fun Y p hp V h=>?_,fibre_pos hh hγ Ξ,hg,reach_price ha,cap hK⟩
   refine (kernel_price ha hK hT Y p h).weaken ?_ (chassis ha)
   have hk:= tag_small Ξ h; have hf : Ξ.tag V ≤ λ' V:= (arranged H V h).trans_le (fibre_price hh hγ Ξ V)
   have he:0 ≤ Ξ.tag V:= Ξ.tagged _
   exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg (α:=ℝ) M)) (pow_nonneg he (p.val+1))).trans (atom_f hg (zero_le_one.trans (cap hK)) (le_trans (mul_le_mul_of_nonneg_right hk (zero_le_one.trans hg)) ((mul_comm ..).le.trans hρ)) he hf _)

variable (hw: R.activities.E=f₁+f₂)
local notation "Q'" => columnPrice θ' ρ λ'
include hL hw
omit hT hρ in
lemma shrimps (i:ℕ) (V:Fin (M+1)) (h:V.val<M) (Y':Finset ℕ) : EstFactor Ξ (κ i) (mantle H f₁ M Y' V (κ i)) A (Q' (κ i) (V.val+1)) Cₑ := by
   rw [other]; intro F X z hX hK' hχ hM hH E _ _ _ U x hz hx
   have hp:= budget H i hh ha hw F X z hX hK' hχ hM hH E U x hz hx
   rw [Set.indicator_of_mem (warm (o:=o) (R:=R) i X z)] at hp ⊢
   let u:= w i+w' i; have hu:0≤u:= hp.nonneg
   let k:= V.val+1
   let j':= ((k.factorial:ℝ))⁻¹
   have hs:1 ≤ (k.factorial:ℝ):= by exact_mod_cast k.factorial_pos
   have hy : ‖j'‖≤ θ':= by rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hs))]; exact (inv_le_one_of_one_le₀ hs).trans (cap hK)
   refine ((Telegraph.powers k hp).smul j').climb ((mul_le_mul_of_nonneg_right hy (pow_nonneg hu _)).trans ?_) (booths ha i h)|>.shimmy ?_
   · exact atom_f hg (zero_le_one.trans (cap hK)) (hL i) hp.nonneg ((le_mul_of_one_le_left hp.nonneg hγ).trans (boosted_e Ξ i)) _
   filter_upwards with t; unfold Insert.mapSmooth; dsimp only []; rw [smul_eq_mul, div_eq_mul_inv]; exact mul_comm ..
lemma completed : Priced Ξ M λ' θ' ρ Cₑ A RuM:= by
   have hh' := authentic hh ha hT hK hg hρ hγ -- args check
   constructor
   · intro Y p ht i h; by_cases hv:i∈ Set.range (Opacity.key S)
     · obtain ⟨i,rfl⟩:=hv; rw [other]; exact stitch (κ i) p _ (insulation H i hh hw)
     rw [keepsOff H _ _ _ hv]; exact hh'.sound _ _ ht i h
   · intro Y p ht i h; by_cases hv:i∈Set.range κ
     · obtain ⟨i,rfl⟩:=hv; exact shrimps hh ha hK hg hγ hL hw i p ht Y
     rw [keepsOff H _ _ _ hv]; exact hh'.cost _ _ ht i h
   · exact hh'.nonneg
   · exact hg
   · exact hh'.effort
   exact hh'.value
local notation "cΔ" => (a/γ) -- δ boost response after buying boosted economic glyph. forecast inventory.
omit hT hρ in
lemma predictable (i:ℕ)(p:Fin (M+1))(hp:p.val<M)(x':Finset ℕ):
   EstFactor Ξ (κ i) ((U! x' p (κ i)).difference (mantle H f₁ M x' p (κ i))) A
     (cΔ*Q' (κ i) (p.val+1)) Cₑ := by
   let z': Fin M:=⟨p.val,hp⟩
   have hb : U! x' p (κ i)= (mage H Ru i).mapSmooth (fun t=>t^(p.val+1)/(p.val+1).factorial):= m_payload w hh.size i x' z'
   rw [hb, other]; intro F X z s' hk hχ hM hH E _ _ _ U x he hv
   let f (t:glyph G _) i':=(mage H t i).value (vary X (U i')) (course X A R.beta z (U i'))
   have hF:= budget H i hh ha hw F X z s' hk hχ hM hH E U x he hv
   have hD:= spatial H i hh ha F X z s' hk hχ hM hH E U x he hv
   have hq:= birth H i hh ha F X z s' hk hχ hM hH E U x he hv
   rw [Set.indicator_of_mem (warm (o:=o) (R:=R) i X z)] at hF hq hD ⊢
   have hx:0≤w i:=hq.nonneg; have hy:0≤w' i:= (mnonneg H i hh).2
   let W:=(w+w') i; have hW : 0≤W:=add_nonneg hx hy; let k:=p.val+1
   have hs:= hq.climb (le_add_of_nonneg_right hy) le_rfl
   have ht i': f Ru i' - f f₁ i'= f f₂ i':= by unfold f; rw [hw, Fort.add_m,Insert.sumTwo];dsimp only;ring
   have hD : Brush j (a*W) (stampFactor H (κ i) vJ) (fun v=> f Ru v-f f₁ v) x:= (hD.shimmy (Eventually.of_forall ht)).climb (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx) hh.pos.le) le_rfl
   let v:= ((k.factorial:ℝ))⁻¹; have hv' : 1≤(k.factorial:ℝ):=by exact_mod_cast k.factorial_pos
   have hξ : ‖v‖≤1:= (Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hv'))).trans_le (inv_le_one_of_one_le₀ hv')
   have h₁:= ((Telegraph.strip k hs hF hD).smul v)
   refine ((h₁).climb ?_ (booths ha i hp)).shimmy (Eventually.of_forall fun x=>?_)
   · have hk: (k:ℝ) ≤ θ':= (Nat.cast_le.mpr hp).trans (le_add_of_nonneg_left (zero_le_one.trans hK.nonneg))
     let c:=(ρ^k)⁻¹*(θ'*ρ); have hc:0≤c:=by unfold c; have h:=cap hK; positivity
     let A:= W^k; have hA:0≤A:=pow_nonneg hW _; let z:= λ' (κ i); have ht:0≤ cΔ := div_nonneg hh.pos.le (zero_le_one.trans hγ)
     have hL:= atom_f hg (zero_le_one.trans (cap hK)) (hL i) hW le_rfl p.val
     calc
       _ ≤ a*((k:ℝ)*A) := by rw [← mul_assoc a]; exact mul_le_of_le_one_left (mul_nonneg (mul_nonneg hh.pos.le (Nat.cast_nonneg _)) hA) hξ
       _ ≤ a*(c*W) := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hk hA).trans (show θ'*A ≤ c*W from hL)) hh.pos.le
       _ = cΔ*(c*(γ*W)) := by field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (boosted_e Ξ i) hc) ht
   dsimp only; rw [Insert.gap,smul_eq_mul,Insert.mapSmooth,Insert.mapSmooth]; dsimp only; rw [← sub_div]; simp only [v,k, div_eq_mul_inv]; ring -- grouping
lemma worksStencil : Quoted Ξ M λ' θ' ρ Cₑ A cΔ U! RuM:= by
   have hu:= authentic hh ha hT hK hg hρ hγ; have h := completed hh ha hT hK hg hρ hγ hL hw
   have ht:0≤cΔ:= div_nonneg hh.pos.le (zero_le_one.trans hγ); refine ⟨hu,h,ht,fun Y p hy i hi=>?_⟩
   by_cases he:i ∈ Set.range κ
   · obtain ⟨v,rfl⟩:=he; exact predictable hh ha hK hg hγ hL hw v p hy Y
   rw [keepsOff H _ _ _ he]; intro F X z hX hK hχ hM hH E _ _ _ V x hb hx
   have hw:= hu.cost Y p hy i hi F X z hX hK hχ hM hH E V x hb hx
   rw [Set.indicator_of_mem (always (o:=o) (R:=R) i hi X z)] at hw ⊢
   exact Brush.zi (Eventually.of_forall fun x=>by simp only [Insert.gap,sub_self]) (mul_nonneg ht hw.nonneg) hw.pos
end Fort
end Retain
end YM.RGLocalTaylor
