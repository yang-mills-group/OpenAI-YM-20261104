import YM.RGLocalTaylor.Retain.Tier
/-! # The actual E singleton.Reusing communication at the first Order
Full integral identity.Global difference only asserted at GERMS for integral
*addition*. Transfers from impulse via real data, every support every mask; no
order truncation beyond `.Mill`. Provides funded correction in final assembled
Reader to be used for step. Does not claim payment for unrealigning properties
on a respelled catalog. Memo: hush `E=0` proxy includes mark-Root NOT forced.
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
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt RG01.Survive
open Mayer goodK Mill
open Match Song Push AnalyticBridge VerifiedReset Collection Extra.Iteration Refrain Geo Quotes
open Captain Ursell Gas Brim
open Fort
namespace Gorge
variable {f' f₁ f₂ : Post.glyph G f} {M:ℕ} (H) (X :Cash W s μ L Q o C T (impulse R f₂ a))
   {e vJ uJ K θ α β Z δ r' d' ρ:ℝ}
   {Ξ : Utopia H j v d r C' χ} {N : Captain H j C' d v Y A b r B q n χ}
set_option quotPrecheck false
local notation "κ" => Opacity.key S
variable (i:ℕ) {z:H.fragrances}
local notation "p₀" => head i (S:=S)
local notation "h₀" => once H i
local notation "y_" => icon H i
local notation "hX" => once X i
local notation "yX" => icon X i
local notation "wX" => (impulse R f₂ a)
local notation "S₀" => reachability y_
local notation "ψM" => cover H (physical H M) (χ:=χ)
local notation "χM" => cover X (physical X M) (χ:=χ)
local notation "ϕM" => cover H (mantle H f₁ M) (χ:=χ)
local notation "w₀" => (wX).activities.E

lemma ixparcel (tp:Stencils T M)(u:Decors (head i (S:=S)) M):
   let z:↥p₀:=⟨κ i,mem_singleton_self _⟩; parcel tp p₀ (leg H (own p₀)) u=tp (own p₀) (u z) (κ i):=by
   intro z; apply Eq.trans (show _ =goodK.payloadT tp p₀ (leg H (own p₀)) u (κ i) from ?_)
   · exact dif_pos (show κ i ∈ p₀ from mem_singleton_self _)
   change Insert.mk _=Insert.mk _; congr! 1; funext F X t; exact Finset.prod_singleton (f:=fun x=> (goodK.payloadT tp p₀ (leg H (own p₀)) u x).value X t) _ -- test name f
-- grade=1 exact label even when histogram counts extras.
lemma unSeal (tp:Stencils T M)(Y:Orders M)(hm:1≤M)(hY:Y.val=1) : cover H tp (χ:=χ) h₀ Y=(tp (own p₀) 0 (κ i)).onLog H χ p₀:=by
   have hp: Start p₀:= fun i hh=> by rw [mem_singleton.mp hh]; exact ⟨Sum.inl (Sum.inl _),rfl⟩
   unfold cover Mill.Total; rw [if_pos ⟨hp,hY.symm ▸ hm⟩]; let z:↥p₀:=⟨κ i,mem_singleton_self _⟩;let s:Decors p₀ M:=fun _=>0
   let r:=fun v: Decors p₀ M=> parcel tp p₀ (leg H (own p₀)) v
   have hh(x:↥p₀): x=z:=Subtype.ext (mem_singleton.mp x.property)
   have hv(v): decorOrder (z:=p₀) (M:=M) v=(v z).val+1:= by unfold decorOrder; rw [sum_eq_single z]; exact fun x _ h=> False.elim (h (hh x)); simp
   have hh' (t:Decors p₀ M)(h:decorOrder t=1):t=s:= funext fun i=> by rw [hh i]; apply Fin.ext; unfold s; rw [Fin.val_zero]; exact Nat.add_right_cancel (show _+1= 0+1 from (hv t).symm.trans h)
   funext V; change validity H p₀ p₀ tp (leg H (own p₀)) (χ:=χ) Y.val V=_; unfold validity; rw [hY, sum_eq_single s]
   · exact congr_arg (fun x=> Insert.onLog x H χ p₀ V) (ixparcel H i tp s)
   · intro b hb h; exact False.elim (h (hh' b (mem_filter.mp hb).2))
   intro h; exact False.elim (h (mem_filter.mpr ⟨mem_univ _, (hv s).trans rfl⟩))

lemma nameCore (g:Post.glyph G f)(k:Finset ℕ)(_hm:1≤M): mantle H g M k 0 (κ i)= mage H g i:=by
   rw [other]; change Insert.mk _=Insert.mk _; congr! 1; funext F X z; simp [mage]
variable {w w':ℕ→ℝ}
local notation "Ru" => R.activities.E
lemma real_head (he:shelved H w)(k:Finset ℕ)(hm:1≤M): physical H M k 0 (κ i)=mage H Ru i:= by
   let t:Fin M:=⟨0,hm⟩
   have hp : physical H M k 0 (κ i)=mantle H Ru M k 0 (κ i):=by rw [other]; exact m_payload w he i k t
   rw [hp]; exact nameCore H i Ru k hm

lemma line_gauge (g:Insert T)(V:Config G c) : g.onLog X χ p₀ V=g.onLog H χ p₀ V:=by
   unfold Insert.onLog Insert.preGauge Insert.inTags; simp_rw [if_pos (icon_auth H i),if_pos (icon_auth X i)]; rfl

lemma line_transport (he:shelved X w')(hm:1≤M)(ha:a≠0) : a • Read.field (fun _ b=> b=1) χM yX=
    (mage H f₂ i).onLog H χ p₀ := by
   let t:Orders M:=⟨1, by omega⟩
   rw [lonely X _ i χM t (fun _=>Iff.rfl), unSeal X _ _ _ hm rfl, real_head X i he _ hm]
   ext V; rw [Pi.smul_apply, line_gauge H X, Fort.boost_lowers H _ _ ha, Insert.log_scale]; rfl -- line_transport defeq

-- if ZERO predictor, all these terms vanish
lemma nullify (τ:Orders M) : cover H (mantle H 0 M) (χ:=χ) h₀ τ=0 := by
   unfold cover Mill.Total; split; next ht=>
      funext V; refine Finset.sum_eq_zero fun u _=>?_
      have hv : parcel (mantle H 0 M) (head i) (leg H (own p₀)) (z:=head i) u=Insert.ofConst 0:= by
         rw [ixparcel H i]
         rw [other]; change Insert.mk _=Insert.mk _; congr! 1; funext F X z
         have hf : mage H 0 i=Insert.ofConst 0:=by rw [show (0:Post.glyph G f)= (0:ℝ)•Ru from (zero_smul ..).symm, Fort.scaled]; change Insert.mk _=Insert.mk _; congr! 1; funext F X z; exact zero_mul _
         rw [hf]; simp [Insert.ofConst] -- powers
      change (parcel (mantle H 0 M) p₀ (leg H (own p₀)) (z:=p₀) u).onLog H χ p₀ V=0; rw [hv]; unfold Insert.onLog Insert.preGauge Insert.inTags Insert.onSlice likely; simp only [if_pos (icon_auth H i),Insert.ofConst,mul_zero,integral_zero,sum_const_zero]
   rfl

variable (take:H.fragrances→ℕ→Prop)
lemma hushRoll : Read.field take (cover H (mantle H 0 M) (χ:=χ)) y_=0:= by ext V; unfold Read.field aliquot; rw [sum_eq_zero (fun j _=>?_),mul_zero]; rfl; exact prod_eq_zero (mem_univ none) (show _=0 from congr_fun (nullify H i (j none) (χ:=χ)) V)

lemma nullsong (TP:Stencils T M) (h:∀ i n,take i n→ n=0): Read.field take (cover H TP (χ:=χ))=0 := by
   ext z V; unfold Read.field; rw [sum_eq_zero (fun j hj=>?_),mul_zero]; rfl
   by_contra hp; obtain ⟨hb,hK⟩:= columnDebt H TP _ hp; have h: z.fst+1≤ 0:= (Beam.on_one z (fun i=> Finset.card_pos.mpr (hK i))).trans (by
       -- avoid Classical.propDecidable equality lint. rw @ fallback.
       refine hb.trans ?_; rw [show atGrade j=0 from h _ _ (mem_filter.mp hj).2]); omega
lemma dialect (TP:Stencils T M) : Read.field (fun _ k=> k=0) (cover H TP (χ:=χ))=0:= nullsong H _ TP (fun _ _=>id)
end Gorge
end Retain
end YM.RGLocalTaylor
