import YM.LocalTaylorR2.Copper.Allow
/-! Polynomial along Strand on actual support. Before transfer by rung. Uniform Complex-polynomial prices at output.
 Exact affine anchor count, all site modes. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open Gas Ursell Trees
variable {ι Z:Type} [Fintype ι] [DecidableEq Z] (Y:ι→Leaf R)(u:ι→ℝ)(hU:Merge.Palette.Plot Y H u)
   (B:_root_.YM.Marker.Census Z)(z:ι→ _root_.YM.Marker.Poly B)
local notation "hd"=> Pressure.temp s
local notation "P!"=> Poly B
local notation "T!"=> turnWeight Y u
variable (l:ℕ)
variable (k:H.fragrances)
local notation "Θ'"=> reachability k
local notation "T'"=> Booking H Y l k -- check args
set_option quotPrecheck false
local notation "Z₀"=> Option (Fin k.1)
open Charge RG01.Survive.Products AnalyticBridge VerifiedReset Next.Foundations
variable {j k' m' n:ℕ} {θ ρ D K e v₀ d b r x Ct b' R' A c' δ :ℝ}
variable (hk:Marker.Tinted G s K d o.a L χ j)(U:StoresR2 H j v₀ d A D k' x n χ)
variable (N:Captain H j Ct d v₀ w A b r b' R' (n+j) χ) {ζ:ℝ}(hB:LocalBookingsR2 ζ c' N.conduit)
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hH:1≤θ)(hp:1≤ρ)(hs:ρ*c'≤1)(hL: Charge.Allows l j θ)(hℓ: ρ^(l+1) ≤ betaF G s L^ζ)(hM:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))
-- collision `Reel.team/profiles`; qualify
open Reel (Filled Strand)
open Reel.Strand (dial)
section sprout
open Reel
variable {Iota:Type} (w:Iota→ℝ)(Z:Iota→ Copper.Stems T) (hg:∀ i:LogIndex c f, Reel.Filled (Reel.Pop H (H.supportP (identityLog i))) 1 w (fun j=> Z j i))
include hg
lemma frost {p₁:Molecule S}(Y:Support c)(hY:H.unionP p₁ ⊆ Y)(q:Paint p₁ n)(he:chooseSlot q≠ Candle.perch n):
     Filled (Pop H Y) (inserts q) w (fun j=> Copper.namesP (Z j) q):= by
   let A:= Pop H Y; let f (j:Iota) := Copper.namesP (Z j) q; let h i j:= Z j (i:↥(logs p₁)).val; let k i:= Series.rank (q i)
   let W i:= ((k i).factorial:ℝ)⁻¹; let v i j:= W i • (h i j ^ k i)
   have hv i: Filled A (k i) w (v i):= by
      have hz : H.supportP (identityLog i.val) ⊆ Y:= (subset_biUnion_of_mem H.supportP ((log_occ _).1 i.property)).trans hY
      have hA : Filled A 1 w (h i):= (hg i).transfers (fun x=>x) (fun _ h=> (show Kept H _ _ from h).mono hz) (fun _ _ _ _=> rfl) (fun _ _ _=>rfl)
      have hc := hA.power (P:=A) (k i) (Kept.fixed 1) (fun _ hx _ hy => Kept.times hx hy) (popPow H)
      rw [one_mul] at hc; exact hc.scaling (W i)
   have ht : f=∏ i,v i:= by
     ext x F X g; unfold f; rw [Finset.prod_apply]; simp_rw [Finset.prod_apply]; apply prod_congr rfl; intro i _; rw [Candle.noOvercharge he]; change _ = ((k i).factorial:ℝ)⁻¹*(h i x F X g)^k i; rw [div_eq_mul_inv]; exact mul_comm ..
   change Filled A (∑ i,k i) w f; rw [ht]; exact Filled.accumulate _ _ _ (fun i _=> hv i) (Kept.fixed 1) (fun _ hx _ hy=>Kept.times hx hy) (popPow H)
end sprout
variable (Φ:Reel.Strand→ Copper.Stems T)
variable (QF:∀ i:LogIndex c f, Filled (Reel.Pop H (H.supportP (identityLog i))) 1 dial (fun j=> Φ j i))
include N QF
open Reel
omit [Fintype ι] in -- using lemma section not include unused
lemma tizzy (q:Orders l) (W:Config G c)(hw:Healthy hd (H.unionP p.val) W): Filled ⊤ q.val Reel.Strand.dial (fun i=> memo W (stock M H χ p (Φ i) q)):=by
   let T₀:=restP M H p; let A:= H.unionP (Θ); let X:= Pop H A
   by_cases h : Orbit.checked M H p ∧ Clear T₀; swap; · simp_rw [stock_off M H χ p _ q h]; exact Filled.steady _ Submodule.mem_top
   by_cases hz : q= Candle.perch l; · unfold stock; simp_rw [if_neg (not_not.mpr hz)]; exact Filled.steady _ Submodule.mem_top
   let Y i (j:Paint T₀ l):= episode H χ Θ (flowerCup M H p (Φ i) j); let C:= univ.filter fun k:Paint T₀ l=> chooseSlot k=q
   have hx: (fun i=> memo W (stock M H χ p (Φ i) q))=∑ j∈ C,(fun i=>memo W (Y i j)):= by
      ext1 i; rw [Finset.sum_apply, ← map_sum]; apply congr_arg; ext V; rw [stock,if_pos hz, stemPlug, if_pos h,Finset.sum_apply]; rfl
   rw [hx]; apply Filled.group; intro i hi; have he:chooseSlot i=q:= (mem_filter.mp hi).2; have ht := ne_of_eq_of_ne he hz
   have hp: Filled X (inserts i) Reel.Strand.dial (fun q=> flowerCup M H p (Φ q) i):=by
      let A₁:Port.Test T:= fun _ X w=> M.paidU X o.a (worldZ X R.beta w); have HA: A₁∈X:= honor M H p h.1.2; let B':= Reel.Strand.dial
      have hh := frost H B' Φ QF (H.unionP p.val) (Finset.biUnion_subset.mpr (fun i hi=> Finset.subset_biUnion_of_mem H.supportP (Finset.sdiff_subset hi))) i ht
      convert (Filled.steady (n:=0) A₁ HA).times (U:=Pop H A) hh (· * ·) (fun _ x _ y=> Kept.times x y) (fun _ _ _=> add_mul ..) (fun _ _ _=> mul_add ..) (popPow H) using 1
      rw [zero_add]
      rfl
   have hI := Reel.pendulum N W hw p.2.2 hp; apply hI.onward
   have hb₀:min (l+1) (inserts i)= q.val:= congr_arg Fin.val he
   have hx:q.val ≤ l:= by
     by_contra hy; apply hz; apply Fin.ext; change q.val=l+1; omega
   omega
omit [Fintype ι] in
lemma fittedFor (q:T')(U:Config G c)(hu:Healthy hd (reachability k) U): Filled ⊤ (ranked H Y l k q) dial (fun j=>memo U (cameoC H χ Y u l k (Φ j) q)):= by
   let f (i:Z₀)(j:Strand):= wiredBox H χ (k.2 i) Y u l (Φ j) (q i)
   have he: (fun j=>memo U (cameoC H χ Y u l k (Φ j) q))=∏ i,(fun j=> memo U (f i j)):= by
      ext1 j; rw [Finset.prod_apply,←map_prod]; apply congr_arg; ext W; rw [Finset.prod_apply]
   rw [he]; refine Filled.accumulate _ _ _ (fun i _=>?_) Submodule.mem_top (fun _ _ _ _ => Submodule.mem_top) (scalar_prod U); exact (tizzy (Palette.team Y (q i).1) H χ (k.2 i) l N Φ QF (q i).2 U (scopeFlag H k U hu i)).scaling (turnWeight Y u (q i).1)
end YM.LocalTaylorR2.Orbit
