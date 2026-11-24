import YM.Comparison.RG02.Adjacent.Equivalent
/-!
# Warp/Ward compatibility

Rank reset sale commutes with full logarithm warp derivative-projections while using THE adjacent
coupling germ. Caller uses `.inverseCurve` with `ω` from curvature-symbol readout on cover (not
computed here) to direct this transport. Also through first discrepancy ideals via `Orbit.follows`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice Marker Multi Wilson Exterior Precision
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace Symmetry Symmetry.Orbit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c:Side}
local notation "φ"=> 𝓝 (0:ℝ)
local notation "X"=> fieldDir G c 1
variable {p : Display (fieldDir G c 1)} {K L : UnitCost} (d:ℤ) (r:ℕ) {m:ℕ→ℤ} (hu:Charge r m p)
  (a b : ℝ→fieldDir G c 1) (hx : glows a) (hy:glows b)
namespace Call
local notation "L₀"=> L.rating
local notation "K₀"=> K.rating
local notation "F"=> born p K d r
def shuttle (L : UnitCost)(t:ℝ):= L.rating t • a (L.enter t)
lemma lifts (K:UnitCost)(he : glows a) : glows (shuttle a K):= K.smooth.smul ((show ContDiffAt ℝ ω a (K.enter 0) from K.borne.symm ▸ he).comp _ K.here)
lemma traveled (L:UnitCost): ∀ᶠ t in φ, Integral.sample t (shuttle a L t)= Integral.sample (L.enter t) (a (L.enter t)) := Eventually.of_forall fun t=> by simp only [Integral.sample,shuttle,smul_smul,UnitCost.enter]
lemma folded (L:UnitCost)(h : Symmetry.Flow a b): Symmetry.Flow (shuttle a L) (shuttle b L) := by
   obtain ⟨u,f,h,hf⟩:= h.bend
   constructor; refine ⟨u,f ∘ L.enter,h.comp L.forward,?_⟩
   filter_upwards [L.forward.eventually hf,(traveled a L).filter_mono nhdsWithin_le_nhds, (traveled b L).filter_mono nhdsWithin_le_nhds] with t ht he hh; rw [he,hh]; exact ht
lemma tag_returns (h : K.Recurs L) : ∀ᶠ t in φ, shuttle a L (K.enter t)=(K₀ t)⁻¹ • a t := by
   filter_upwards [h.stays,h.pairs] with t ht he; unfold shuttle; rw [ht,(show L.enter (K.enter t)=t from he)]
include hx
lemma escort (r:ℕ)(h:∀ i≤r, ContDiff ℝ ω (p i)): ContDiffAt ℝ ω (fun t=>cover p r t (a t)) 0:= by unfold cover; exact ContDiffAt.sum (fun i hi=> ((Complex.ofRealCLM.contDiff.contDiffAt).pow i).mul ((h i (mem_range_succ_iff.mp hi)).contDiffAt.comp _ hx))
lemma assessed (r:ℕ)(h:∀ i≤r, ContDiff ℝ ω (p i)) (k:ℕ)(hk:k≤ r) : motion (fun t=> cover p r t (a t)) k=patrol k p a := by
   unfold cover patrol; let f (i:ℕ):= p i ∘ a; have hp i (he:i∈range (r+1)) : ContDiffAt ℝ ω (f i) 0:= (h i (mem_range_succ_iff.mp he)).contDiffAt.comp _ hx
   change motion (fun t=> ∑ i∈range (r+1), (t:ℂ)^i*f i t) k= _
   rw [msum _ (f:=fun i (t:ℝ)=> (t:ℂ)^i*f i t) fun i hi=>(Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul (hp i hi),
    sum_congr rfl (g:=fun i=> if i≤ k then motion (f i) (k-i) else 0) (fun i hi=> mono_price (hp i hi)), ← sum_filter]
   rw [show (range (r+1)).filter (fun z=> z ≤ k) = range (k+1) by ext i; simp only [mem_filter,mem_range]; omega, ← Finset.sum_range_reflect]; apply sum_congr rfl; intro i hi; simp only [Nat.add_sub_cancel]; rw [Nat.sub_sub_self (mem_range_succ_iff.mp hi)]
omit hx
include hu
lemma salable (K:UnitCost) (i:ℕ): ContDiff ℝ ω (born p K d r i) := by simp_rw [show born _ _ _ _ _= _ from funext (message K d r hu i)]; exact ContDiff.sum fun i hi=> ContDiff.sum fun j _=> contDiff_const.mul (levelJet ((hu i (mem_range_succ_iff.mp hi)).smooth.contDiffAt) j).smooth
include hx hy
lemma readable (h:Sheet r p) (w:Symmetry.Flow a b) (K: UnitCost)(i:ℕ)(hi:i≤ r): patrol i (born p K d r) a=patrol i (born p K d r) b:= by
   let P:= K.rating; let L:= K.inverseCurve; let f (t:ℝ):ℂ:= ↑(P t^d); have hc:= K.rightInverse
   have H:= folded a b L w
   let A:= shuttle a L; let B:= shuttle b L
   have ha: glows A:= lifts a L hx; have hb: glows B:= lifts b L hy
   let E (a:ℝ→X) := fun t:ℝ=> cover p r t (a t)
   have hP : Shadow r (E A) (E B):= by
         refine ⟨escort A ha r h.known, escort B hb r h.known,fun i hi=>?_⟩; unfold E; rw [assessed _ ha r h.known i hi, assessed _ hb r h.known i hi, h.follows A B H ha hb i hi]
   have ht : Shadow r (fun t=> f t*E A (K.enter t)) (fun t=> f t*E B (K.enter t)) := (Shadow.refl (f:=f) (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (K.spin d))).product (hP.respite K)
   have hv(a:ℝ→fieldDir G c 1): (fun t=> f t*E (shuttle a L) (K.enter t))=ᶠ[φ]fun t=> ages p d r t (P t) (a t):= (tag_returns a hc).mono fun t ht=> by dsimp only [E,L]; rw [ht]; rfl
   rw [← assessed a hx r (fun i _=> salable d r hu K i) i hi, ← assessed b hy r (fun i _=> salable d r hu K i) i hi,
     (curvedAt d r hu K a hx).aligns i hi, (curvedAt d r hu K b hy).aligns i hi]; exact ((mgerm (hv a)).symm.trans (ht.aligns i hi)).trans (mgerm (hv b))
omit hx hy
lemma certified (K:UnitCost)(h:Sheet r p): Sheet r (born p K d r):= ⟨fun i _=> salable d r hu K i,fun x y w he hv=> readable d r hu x y he hv h w K⟩
end Call

-- orientation signed/transl
lemma point (Z:X→L[ℝ]X)(hp :∀ i≤r,p i ∘ Z=p i)(K:UnitCost)(i:ℕ): (born p K d r i) ∘ Z= born p K d r i := by
   ext1 v; unfold born; rw [Function.comp_apply]; apply congr_fun (g:=motion _) (congrArg motion _)
   funext t; unfold ages cover; rw [← map_smul]; refine congr_arg₂ _ rfl (sum_congr rfl fun j hj=> ?_)
   rw [show p j (Z _)=_ from congr_fun (hp j (mem_range_succ_iff.mp hj)) _]
end YM.Comparison.RG02.Adjacent
