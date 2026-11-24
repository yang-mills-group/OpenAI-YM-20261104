import YM.LocalTaylorR2.Exponent.Kiosk

/-!
 # Assembly at HIGH rank perch gets new momentum budget (including sums). One actual price after burn. interpolation χ inside Poly growth Bank. No extra exp Q.loans at this stage.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open PhysicalNext.Repeat Reel Strand Candle Tender Mesh LocalTaylorR2.Price Charge RG01.Survive
variable (H:Cash W s μ L Q o C T R)(Ξ:Observatory G)
variable (U:H.ThinP){q:Orders k}{b t w A' r D' V' e ρ θ ζ c':ℝ} (N:Captain H j b t v w A A' r D' e (n+j) χ) (hB:LocalBookingsR2 ζ c' N.conduit)(M:StoresR2 H j v t A D l x n χ) (F': Wealth Ξ H V' n x l m N.conduit k ρ)
local notation "Θ" t=> replay (weightLog H) (Ξ.upgrade H k) (dial t*ρ^k)
local notation:max "Ig" i:max => Mesh.issue H i χ U (l:=k)
local notation:max "Z!"=> schemePrice (l:=k) N D x θ U
local notation "X"=> Ξ.upgrade H k
lemma lowtime (q:ℕ)(ρ:ℝ)(h:1≤ρ):∃ x:Strand, dial x=(ρ^q)⁻¹ ∧ 0≤dial x:=by
 let v:=(ρ^q)⁻¹; have hx:0≤v:=by unfold v; positivity
 exact ⟨⟨v,by exact ⟨by linarith,inv_le_one_of_one_le₀ (one_le_pow₀ h)⟩⟩,rfl,hx⟩
lemma menu (k:ℕ)(ρ:ℝ): replay (weightLog H) (Ξ.upgrade H k) (dial Strand.bud*ρ^k) =weightLog H:=by unfold replay dial Strand.bud; simp only [zero_mul,zero_smul,add_zero]
lemma erg (i:Strand)(he: dial i=(ρ^k)⁻¹)(h:1≤ρ): (Θ i)=Ξ.upgrade H k:=by unfold replay; rw [he, inv_mul_cancel₀ (pow_ne_zero _ (zero_lt_one.trans_le h).ne'), one_smul]; abel
include M F' N
variable (h:1≤ρ)(ht:1≤θ)
include ht h
lemma perchless (i:Orders k)(he:i≠ Candle.perch k) : Items H U (Ig (X) i) ∧ ∀ (V:Config G c), Healthy (Pressure.temp s) (H.smallAt U) V →
   Ore V (Ig (X) i) v (Z! i) j ∧ Ore V ((Ig (X) i)-sprig H χ U i) v (if i=0 then 0 else spelling k*(ρ^k)⁻¹* Z! i) j:= by
 obtain ⟨u,hu,hU⟩:= lowtime k ρ h; have hw p := kiosq H Ξ U N M F' p i he ht -- sec comp
 rw [← erg H Ξ u hu h]; refine ⟨(hw u).1,fun V hv=>⟨(hw u).2 V hv,?_⟩⟩; -- get pend.Ann
 rw [show Candle.sprig H χ U i= Ig (Θ Strand.bud) i by rw [menu,pristine]]; split; rename_i hx; swap
 · intro E _ _ _ V' x' hv' hm'
   have hy:ContinuousAt V' x':= continuousAt_pi.mpr fun i=> (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (hm'.atLink i).smooth.continuousAt.tendsto
   let f' t:=Ig (Θ t) i; let X' j := tolling (n:=k) u j • f' (stems j); have hh: i.val ≤ k:= by by_contra ht'; apply he; apply Fin.ext; change _ = k+1; omega
   have hH: (f' u-f' bud)∘V'=ᶠ[𝓝 x'] fun x=>∑ j,X' j (V' x):=by
     have hz: f' u-f' Strand.bud =ᶠ[𝓝 V] ∑ j,X' j:= (line_eq V _ _).1 (by rw [map_sub,map_sum]; unfold X'; simp_rw [memoScale]; exact Strand.rates u ((lineage H Ξ U N F' V he hv).onward hh))
     refine (hz.comp_tendsto (show Tendsto V' (𝓝 x') (𝓝 V) from (by rw [← hv']; exact hy))).mono (fun i he=> by simpa only [Function.comp_apply,Finset.sum_apply] using he)
   have hp := Brush.spree (Finset.univ (α:=Fin (k+1))) (fun j x=> X' j (V' x)) _ zero_le_one (fun y _ => ((hw (stems y)).2 V hv E V' x' hv' hm').smul (tolling u y))
   apply (hp.shimmy hH).climb _ le_rfl; simp_rw [Real.norm_eq_abs]; rw [← Finset.sum_mul,← hu]; exact mul_le_mul_of_nonneg_right (Strand.legacy u hU k) (LocalTaylorR2.Price.positional N M ht _ _)
 rw [hx,placid H U (Θ u) (Θ Strand.bud),sub_self]; exact fun E _ _ _ _ x _ _=> Brush.zi (Eventually.of_forall fun _=>rfl) le_rfl zero_le_one
-- high perch actual-minus-comparison all at *same* geometry.The operator book.
lemma highCatch :
   let q:= Candle.perch k; let f (i:Orders k):ℝ:= if i=0 then 0 else spelling k*(ρ^k)⁻¹*Z! i
   let D₀:= (∑ i∈ univ.erase q,f i)
   Items H U (Ig (X) q) ∧ ∀ (V:Config G c), Healthy (Pressure.temp s) (H.smallAt U) V →
     Ore V (Ig (X) q-Candle.sprig H χ U q) v D₀ j:=by
 intro q f D₀; let Y:= Ig (X); let f₀:= Candle.sprig H χ U (l:=k)
 have he : Y q= f₀ q- ∑ i∈ univ.erase q,(Y i-f₀ i) := by
    ext W; have h : (∑ i:Orders k,Y i W)=∑ i,f₀ i W := (Mesh.floorplan H (X) χ U W k).symm.trans (Candle.equality H χ U W k); rw [← add_sum_erase _ _ (mem_univ q),← add_sum_erase _ (fun i=> f₀ i W) (mem_univ q)] at h
    rw [Pi.sub_apply,Finset.sum_apply]; simp_rw [Pi.sub_apply,Finset.sum_sub_distrib]; linarith
 have hu i:= Candle.indexed H χ U (l:=k) i; have hx {i:Orders k} (hi:i∈univ.erase q) := perchless H Ξ U N M F' h ht i (ne_of_mem_erase hi)
 have hz {f g:Config G c→ℝ}(h:Items H U f)(h':Items H U g): Items H U (f-g):=⟨fun z V=> congr_arg₂ (·-·) (h.1 z V) (h'.1 z V),h.2.1.sub h'.2.1, fun V Z hV=>congr_arg₂ (·-·) (h.2.2 V Z hV) (h'.2.2 V Z hV)⟩
 let R i:=Y i-f₀ i; have hX i (hi:i∈ univ.erase q):Items H U (R i):=hz (hx hi).1 (hu i); change Items H U (Y q) ∧ ∀ V, Healthy (Pressure.temp s) (H.smallAt U) V→ Ore V (Y q-f₀ q) v D₀ j; rw [he]; constructor
 · refine hz (hu q) ⟨fun z V=>?_,?_,fun V V' hV=>?_⟩
   · rw [Finset.sum_apply, Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> (hX i hi).1 z V
   · show Measurable (∑ i∈ univ.erase q,R i); simpa only [←Finset.sum_apply] using (Finset.measurable_fun_sum (f:=R) (univ.erase q) (fun i h=> (hX i h).2.1))
   rw [Finset.sum_apply, Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> (hX i hi).2.2 V V' hV
 intro U' h E _ _ _ V₀ x₀ hv hV; rw [sub_right_comm,sub_self,zero_sub]; simp_rw [Function.comp_def,Pi.neg_apply,Finset.sum_apply]; exact (Brush.spree _ (fun i v=> R i (V₀ v)) f zero_le_one fun i hi=> ((hx hi).2 U' h).2 E V₀ x₀ hv hV).opposite
end YM.LocalTaylorR2.Exponent
