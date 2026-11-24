import YM.LocalTaylorR2.Grafting.Depot
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
variable {Iota:Type} (w:Iota→ℝ)(m₁ m₂:Iota)(hm:w m₁=0)(hm':w m₂=1) (y t: Reel.Scroll G f)(Q':∀ i:Iota,Cash W s μ L Q o C T (Reel.bend R (y+w i • t)))
include hm hm' Q'
lemma fungible {p₁:Molecule S}(Y:Support c)(hY:H.unionP p₁ ⊆ Y)(q:Paint p₁ n)(he:chooseSlot q≠ Candle.perch n):
     Filled (Pop H Y) (inserts q) w (fun j=> Reel.press H (y+ w j • t) q):= by
   let A:= Pop H Y; let f (j:Iota) := Reel.press H (y+ w j • t) q; let h i j:= sprout H (y+ w j • t) (i:↥(logs p₁)).val; let k i:= Series.rank (q i)
   let Z i:= ((k i).factorial:ℝ)⁻¹; let v i j:= Z i • (h i j ^ k i)
   have hv i: Filled A (k i) w (v i):= by
      have hz : H.supportP (identityLog i.val) ⊆ Y:= (subset_biUnion_of_mem H.supportP ((log_occ _).1 i.property)).trans hY
      have hc := (sprout_filled H w m₁ m₂ hm hm' y t Q' _ hz).power (P:=A) (k i) (Kept.fixed 1) (fun _ hx _ hy => Kept.times hx hy) (popPow H)
      rw [one_mul] at hc; exact hc.scaling (Z i)
   have ht : f=∏ i,v i:= by
     ext x F X g; unfold f; rw [Finset.prod_apply]; simp_rw [Finset.prod_apply]; apply prod_congr rfl; intro i _; rw [Candle.noOvercharge he]; change _ = ((k i).factorial:ℝ)⁻¹*(h i x F X g)^k i; rw [div_eq_mul_inv]; exact mul_comm ..
   change Filled A (∑ i,k i) w f; rw [ht]; exact Filled.accumulate _ _ _ (fun i _=> hv i) (Kept.fixed 1) (fun _ hx _ hy=>Kept.times hx hy) (popPow H)
end sprout
variable (φ:Reel.Scroll G f)
local notation "Ω'"=> (fun i:Reel.Strand=> R.activities.E+Reel.Strand.dial i • φ)
variable (QF:∀ i:Reel.Strand,Cash W s μ L Q o C T (Reel.bend R (R.activities.E+Reel.Strand.dial i • φ)))
include N QF
open Reel
omit [Fintype ι] in -- using lemma section not include unused
lemma nifty (q:Orders l) (W:Config G c)(hw:Healthy hd (H.unionP p.val) W): Filled ⊤ q.val Reel.Strand.dial (fun i=> memo W (stalk M H χ p (R.activities.E+Reel.Strand.dial i • φ) q)):=by
   let T₀:=restP M H p; let A:= H.unionP (Θ); let X:= Pop H A
   by_cases h : Orbit.checked M H p ∧ Clear T₀; swap; · simp_rw [stalk_off M H χ p _ q h]; exact Filled.steady _ Submodule.mem_top
   by_cases hz : q= Candle.perch l; · unfold stalk; simp_rw [if_neg (not_not.mpr hz)]; exact Filled.steady _ Submodule.mem_top
   let Y i (j:Paint T₀ l):= episode H χ Θ (bloomP M H p (R.activities.E+Reel.Strand.dial i • φ) j); let C:= univ.filter fun k:Paint T₀ l=> chooseSlot k=q
   have hx: (fun i=> memo W (stalk M H χ p (R.activities.E+Reel.Strand.dial i • φ) q))=∑ j∈ C,(fun i=>memo W (Y i j)):= by
      ext1 i; rw [Finset.sum_apply, ← map_sum]; apply congr_arg; ext V; rw [stalk,if_pos hz, stemP, if_pos h,Finset.sum_apply]; rfl
   rw [hx]; apply Filled.group; intro i hi; have he:chooseSlot i=q:= (mem_filter.mp hi).2; have ht := ne_of_eq_of_ne he hz
   have hp: Filled X (inserts i) Reel.Strand.dial (fun q=> bloomP M H p (R.activities.E+Reel.Strand.dial q • φ) i):=by
      let A₁:Port.Test T:= fun _ X w=> M.paidU X o.a (worldZ X R.beta w); have HA: A₁∈X:= honor M H p h.1.2; let B':= Reel.Strand.dial
      have hh := fungible H B' Strand.bud Strand.lip rfl rfl R.activities.E φ QF (H.unionP p.val) (Finset.biUnion_subset.mpr (fun i hi=> Finset.subset_biUnion_of_mem H.supportP (Finset.sdiff_subset hi))) i ht
      convert (Filled.steady (n:=0) A₁ HA).times (U:=Pop H A) hh (· * ·) (fun _ x _ y=> Kept.times x y) (fun _ _ _=> add_mul ..) (fun _ _ _=> mul_add ..) (popPow H) using 1
      rw [zero_add]
      rfl
   have hI := Reel.pendulum N W hw p.2.2 hp; apply hI.onward
   have hb₀:min (l+1) (inserts i)= q.val:= congr_arg Fin.val he
   have hx:q.val ≤ l:= by
     by_contra hy; apply hz; apply Fin.ext; change q.val=l+1; omega
   omega
omit [Fintype ι] in
lemma fuss (q:T')(U:Config G c)(hu:Healthy hd (reachability k) U): Filled ⊤ (ranked H Y l k q) dial (fun j=>memo U (blueC H χ Y u l k (R.activities.E+Reel.Strand.dial j • φ) q)):= by
   let f (i:Z₀)(j:Strand):= starBox H χ (k.2 i) Y u l (R.activities.E+Reel.Strand.dial j • φ) (q i)
   have he: (fun j=>memo U (blueC H χ Y u l k (R.activities.E+Reel.Strand.dial j • φ) q))=∏ i,(fun j=> memo U (f i j)):= by
      ext1 j; rw [Finset.prod_apply,←map_prod]; apply congr_arg; ext W; rw [Finset.prod_apply]
   rw [he]; refine Filled.accumulate _ _ _ (fun i _=>?_) Submodule.mem_top (fun _ _ _ _ => Submodule.mem_top) (scalar_prod U); exact (nifty (Palette.team Y (q i).1) H χ (k.2 i) l N φ QF (q i).2 U (scopeFlag H k U hu i)).scaling (turnWeight Y u (q i).1)
end YM.LocalTaylorR2.Orbit
