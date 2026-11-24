import YM.LocalTaylorR2.Grafting.Truss
import YM.LocalTaylorR2.Grafting.Shell
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
abbrev chef (F':∀ k:H.fragrances,Finset (Booking H Y l k))(φ:Reel.Scroll G f):= fun i=> blueS H χ Y u B z l i φ (F' i)
-- `E'=E` specialization true, on Moon filter
omit [Fintype ι] in
lemma chalk (F':∀ k:H.fragrances,Finset (Booking H Y l k)) (hF:∀ i q,q∈ F' i → ranked H Y l i q≤l) : chef H χ Y u B z l F' R.activities.E = fun i=>measureS H χ Y u B z l i (F' i):=by
   ext1 i; ext1 V; apply sum_congr rfl; intro j hi; unfold blueSlice slice; congr! 3; unfold blueC channel; apply prod_congr rfl; intro k _; unfold starBox state; rw [certified_here]; exact (Finset.single_le_sum (f:=fun m=>(j m).2.val) (fun _ _=>Nat.zero_le _) (mem_univ k)).trans (hF _ _ hi)

open Reel
variable {F': ∀ k:H.fragrances,Finset (Booking H Y l k)}(hF:∀ i q,q∈ F' i → ranked H Y l i q≤l)
variable (φ:Reel.Scroll G f)(QF:∀ i:Reel.Strand,Cash W s μ L Q o C T (Reel.bend R (R.activities.E+Reel.Strand.dial i • φ)))
include N QF hF
-- explicit displacement. use stencil & row nerve
omit [Fintype ι] in
lemma thrice (i:B.Mode) (U₀:Config G c)(hv:Healthy hd (reachability k) U₀) : Filled ⊤ l dial (fun q=> tint U₀ (fun U=> (chef H χ Y u B z l F' (R.activities.E+dial q • φ) k U).part i)):= by
   let W q:= R.activities.E+dial q • φ; let U':= U₀; let v j q (V:Config G c):= (blueSlice H χ Y u B z l k (W q) j V).part i
   have he q: (fun U=> (chef H χ Y u B z l F' (W q) k U).part i)= ∑ j∈F' k,v j q:=by funext x; unfold chef blueS v; rw [Finset.sum_apply]; exact Poly.part_sum ..
   change Filled _ _ _ (fun q=>tint U₀ (fun U=>(chef H χ Y u B z l F' (W q) k U).part i))
   simp_rw [he,map_sum]; convert! Filled.group (P:=⊤) (w:=dial) (n:=l) (F' k) (fun x q=> tint U₀ (v x q)) ?h using 1; swap
   · intro j hi
     let X':=(petition H Y B z l k j).part i; let f q:= coeff H k • blueC H χ Y u l k (W q) j
     have he : v j=fun k x=> f k x • X':=by funext m x; exact (Complex.real_smul ..).symm
     rw [he]; exact (plaster X' U₀ f ((fuss H χ Y u l k N φ QF j U₀ hv).scaling _)).onward (hF _ _ hi)
   ext1 q; rw [Finset.sum_apply]
section purchases
variable [Fintype Z] (q₁:Z→ℝ)(hQ:∀ i,0<q₁ i)(hq:∀ i,Marker.Poly.price q₁ (z i) ≤ 1) (Ra:Z→Site c) (hr:∀ i, GridApprox.Nil.Scoped {x| Ra x∈(Y i).crest.image S.ratio.parent} (z i))
local notation "ℛ"=> shop H B q₁ Ra
variable {P':BudgetPoint}{e:ℝ} (q:Strand) (hx:0 ≤ dial q)
omit N hF QF -- last include?
omit [Fintype Z] [Fintype ι] in
lemma pennantG (f:Strand→ H.fragrances→ Config G c→ Poly B)(h:∀ i,shop H B q₁ Ra P' (f i) e)(hv:∀ i U,Healthy P'.threshold (reachability i) U → ∀ m,Filled ⊤ l dial (fun j=> tint U (fun V=>(f j i V).part m)))(hx:0 ≤ dial q): ℛ P' (f q-f Strand.bud) (Strand.spelling l * dial q * e):=by
   let F i:= (Strand.tolling q (i:Fin (l+1)):ℂ) • f (Strand.stems i)
   have hz(i:Fin (l+1)):ℛ P' (F i) (|Strand.tolling q i| * e):=by
     have hp := shopScale H B q₁ Ra (h (Strand.stems i)) (Strand.tolling q i); rw [Complex.norm_real,Real.norm_eq_abs] at hp; exact hp
   have ht:= shopVector H B q₁ Ra univ F _ (fun i _=> hz i); obtain ⟨g,hg,hG,hP⟩:= h q
   have hy:= budget_nonneg (hG 0)
   refine opened _ _ _ _ (shopG _ _ _ _ ht (shopSub _ _ _ _ (h q) (h Strand.bud)) ?_) ((Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right (Strand.legacy q hx l) hy))
   intro i U hG m; let Y j:= tint U (fun V=>(f j i V).part m)
   rw [show tint U (fun V=> ((f q - f Strand.bud) i V).part m) = Y q - Y Strand.bud from map_sub (tint U) (fun V=>(f q i V).part m) (fun V=>(f Strand.bud i V).part m), Strand.rates q (show Filled ⊤ l Strand.dial Y from hv i U hG m)]; unfold F
   let w i:ℝ:= Strand.tolling q (i:Fin (l+1)); let p':= Config G c -- remove since f shadows Fine? config c.
   let X (j:Fin (l+1)): Config G c→ℂ:= fun V=>(f (Strand.stems j) i V).part m
   have hy: (fun V=> ((∑ i',(w i':ℂ) • f (Strand.stems i')) i V).part m)= ∑ j,(w j:ℂ) • X j:=by
      funext V; simp_rw [Finset.sum_apply,Pi.smul_apply,Poly.part_sum,Poly.part_smul]; rfl
   change tint U (fun V=> ((∑ i',(w i':ℂ) • f (Strand.stems i')) i V).part m)= _
   rw [hy,map_sum]; exact sum_congr rfl (fun i _=>scalarG ..)
include hF QF hx hQ hq hr hU
open Tail
lemma steadyG (P':BudgetPoint)(he:P'.threshold=Pressure.temp s)(hb:P'.B=radiusB s)(D:Target.Expense Q) {ε:ℝ} (hp:Quotes.preExponent P' ≤ D.earn)(ht: Stamp T)(hR:rise Q D L W μ s o P'.order P'.power l χ ε)
  (r':ℕ)(hL:r'≤l+1)(hn:∀ p q,q∈F' p → r'≤ ranked H Y l p q):
    ℛ P' (chef H χ Y u B z l F' (R.activities.E+Reel.Strand.dial q • φ)-(fun i=>measureS H χ Y u B z l i (F' i))) (Strand.spelling l * dial q * (betaF G s L^requested r' ε)):=by
   rw [← chalk H χ Y u B z l F' hF]
   obtain ⟨A,a',C,X',v₁,t',r,B',D',x',b,y,K,θ,ρ,w,l',n,hP,hFee,h⟩:= hR; obtain ⟨N,-⟩:= h _ _ _ _ ht _ _ H
   let f j:=chef H χ Y u B z l F' (R.activities.E+Reel.Strand.dial j • φ)
   rw [show chef H χ Y u B z l F' R.activities.E=f Strand.bud from by unfold f; rw [show dial Strand.bud=0 from rfl,zero_smul,add_zero]]
   apply pennantG H B l q₁ Ra q f (fun i=> ?_) (fun i U h m=>thrice H χ Y u B z l i N hF φ QF m U (he ▸ h)) hx
   exact blueParts H χ Y u hU B z l q₁ hQ hq Ra hr P' he hb F' _ (J':=QF i) D hp ⟨A,a',C,X',v₁,t',r,B',D',x',b,y,K,θ,ρ,w,l',n,hP,hFee,h⟩ ht hL hn
end purchases
end YM.LocalTaylorR2.Orbit
