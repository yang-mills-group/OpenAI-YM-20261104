import YM.LocalTaylorR2.Orbit.Apert
import YM.MergeProof.Sate
/-! Spin, actual nilpotent product (after all unfiltered Refs). -/
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
local notation "t"=> Tickets (sign Y S)
local notation "hd"=> Pressure.temp s
local notation "P!"=> Poly B
local notation "T!"=> turnWeight Y u
variable (l:ℕ)
abbrev Travel (S:StepData c f)(Y:ι→Lotus.Leaf R)(l:ℕ) := Tickets (Palette.sign Y S) × Orders l
abbrev poles (i:t) := ∏ j∈i.val,z j
abbrev state (i:Travel S Y l)(V:Config G c):ℝ:= T! i.1*Orbit.graded (Palette.team Y i.1) H χ p i.2 V
abbrev station (i:Travel S Y l)(V:Config G c): P!:= ((state H χ p Y u l i V:ℂ)) • poles Y B z i.1
-- algebra via t diagonal capture, jet sign (one REAL marker per field stencil token, invariant even φ positive). No repeated powers collapsed at p-limit. holds ALL Polys with squarezero generators.
lemma tasted_color (V:Config G c) (hv:Healthy hd (H.smallAt p) V):
    Switch.sound z (Palette.vote Y H χ u Θ V)=∑ i:Travel S Y l, station H χ p Y u B z l i V:=by
  let f (i:t) :Ways ι:= click i.val (turnWeight Y u i * deck (Palette.team Y i) H χ p V)
  have he: vote Y H χ u Θ V=∑ i:t,f i:=by
    ext h₀ p'; change color Y H χ V _ _=_; unfold color; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i _; rw [amplitudes,
      show act Y H χ V (Θ) i=deck (Palette.team Y i) H χ p V from (dose _ H χ p V).trans (masked_eq _ _ _ _ hv)];
    unfold f click; split <;> ring -- names ω.S
  rw [he,summed z _ f _ (fun i _=> (show Switch.Paid (fun _:Unit=>f i) ‖turnWeight Y u i * deck (Palette.team Y i) H χ p V‖ from paidClick _ (norm_nonneg _) (fun _=>le_rfl))),Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>?_
  unfold f; rw [gather,Orbit.beams_split (l:=l),Finset.mul_sum, Complex.ofReal_sum,Finset.sum_smul]

-- variants for product/sounds with shared origin; x→real; no independence of noise
variable (k:H.fragrances)
abbrev Booking := Option (Fin k.1) → Travel S Y l
local notation "Θ'"=> reachability k
local notation "T'"=> Booking H Y l k -- check args
set_option quotPrecheck false
local notation "Z₀"=> Option (Fin k.1)
def stampX : (Poly B) →ₗ[ℂ] (Poly B) where
  toFun p i:= if i=B.quiet then 0 else p.part i
  map_add' a b:= by
    ext i :1; change (if i=B.quiet then 0 else (a+b).part i) = (if i=B.quiet then 0 else a.part i)+(if i=B.quiet then 0 else b.part i); split; rw [add_zero]; rfl
  map_smul' a p:= by ext i :1; change (if i=B.quiet then 0 else (a • p).part i) = a*(if i=B.quiet then 0 else p.part i); split; rw [mul_zero]; rfl
-- define before m; commute
lemma stampX_at (p: P!) (i:B.Mode): (stampX B p).part i=if i=B.quiet then 0 else p.part i:= rfl

abbrev currentPoly (q:T') := ∏ i:Z₀,poles Y B z (q i).1
abbrev petition (q:T') := stampX B (currentPoly H Y B z l k q)
abbrev coeff : ℝ:= coefficient H.seam k.2/(k.fst+1).factorial
abbrev channel (q:T') (U:Config G c):ℝ:=∏ i:Z₀,state H χ (k.2 i) Y u l (q i) U
abbrev slice (q:T') (U:Config G c): P!:= ((coeff H k* channel H χ Y u l k q U:ℝ):ℂ) • petition H Y B z l k q

lemma scopeFlag (V:Config G c)(he:Healthy hd Θ' V)(i: Z₀): Healthy hd (H.smallAt (k.2 i)) V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ k.snd) (mem_univ i)) he
variable (hx: ∀ i, z i*z i=0)
include hU hx
lemma prong (U:Config G c)(hp:Healthy hd Θ' U):
    Switch.sound z (Palette.song Y H χ u k U)=∑ q:T', ((coeff H k* channel H χ Y u l k q U:ℝ):ℂ) • currentPoly H Y B z l k q:= by
  let f (i:Z₀):=vote Y H χ u (k.2 i).val U
  let v : Ways ι:= fun _ _=>coeff H k; let c:=coeff H k
  let e i:= Palette.tune Y H u 0 0 (k.2 (i:Z₀)).val
  have he i: Switch.Paid (fun _: Unit=>f i) (e i):= (Palette.aca Y H χ u hU (k.2 i) 0).toPoint _ U -- order
  have ht: song Y H χ u k U=v*∏ i,f i:=by
    unfold song Cash.trainedMill Gas.term; ext x y; simp only [Pi.mul_apply,Finset.prod_apply,v,coeff ,f,vote, Cash.entriesMill]; ring
  let f' := fun i (_:Unit) => f i
  have hc : Switch.Paid (fun _:Unit=>v) ‖coeff H k‖:= constant (fun _=> c) (norm_nonneg _) (fun _=> le_rfl)
  obtain ⟨X,hX⟩:= hc.works ()
  obtain ⟨g,hg⟩:= (Paid.prod univ f' e (fun i _=> he i)).works ()
  rw [show (∏ i,f' i) ()=∏ i,f i from by rw [Finset.prod_apply]] at hg
  rw [ht,mul_sounds z hx (show Models v X from hX) hg]
  rw [show v=(fun _ _=>c) from rfl,Switch.const_sounds,Switch.product z hx (c:=f) _ _ (fun i _=>he i),Poly.product_bead]
  have he i: Merge.Switch.sound z (f i)=∑ t₀:Travel S Y l, station H χ (k.2 i) Y u B z l t₀ U:= tasted_color H χ (k.2 i) Y u B z l U (scopeFlag H k U hp i)
  simp_rw [he]; rw [Fintype.prod_sum (f:=fun i x=>station H χ (k.2 i) Y u B z l x U),Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> ?_; unfold station; rw [Finset.prod_smul,← Complex.ofReal_prod]; unfold c; rw [smul_smul,Complex.ofReal_mul] -- cast mult

variable (hX:∀ i,(z i).part B.quiet=0)
include hX
lemma awakened (U:Config G c): Photo.headSheet Y H χ u B z k U= masked hd (reachability k) (fun U=>∑ q:T', slice H χ Y u B z l k q U) U:=by
  by_cases ht: Healthy hd (Θ') U; swap
  · rw [masked_ne _ _ _ _ ht]
    -- doesn't need Photo.Usable: tone zero via Field.V. proof
    let f:=Palette.song Y H χ u k; have hv V: f U V=0:=by ext i; exact Classical.byContradiction fun hx=>ht ((Palette.permits ..).2.2.2 U hx)
    unfold Photo.headSheet; rw [show Photo.tones Y H χ u k U= (fun _ _=>0) from ?_, Switch.const_sounds]; · simp
    funext t₀ s; change f U t₀ s-f U 0 ∅=0; rw [hv,hv]; simp
  rw [masked_eq _ _ _ _ ht];
  have hv:= prong H χ Y u hU B z l k hx U ht
  let f:= Palette.song Y H χ u k U; let c:=f 0 ∅; let g : Ways ι:=fun _ _=> -c
  have hL : Switch.Paid (fun _:Unit=> g) ‖-c‖:= constant (fun _=>-c) (norm_nonneg _) (fun _=> le_rfl)
  have hc:= hL.works ()|>.choose_spec
  have hh: Switch.Paid (fun _:Unit=>f) (Palette.lace Y H u 0 k):=(Palette.fair Y H χ u hU k 0).toPoint _ U
  have h : stampX B (sound z f)= ∑ q:T', slice H χ Y u B z l k q U:=by unfold f; rw [hv]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> map_smul ..
  rw [←h]; ext i :1
  unfold Photo.headSheet; rw [show Photo.tones Y H χ u k U=f+g from by funext a v; exact sub_eq_add_neg .., Switch.add_sounds z (show Models f _ from (hh.works ()).choose_spec) hc,Poly.part_plus, stampX_at, Switch.const_sounds]
  have hz : (sound z f).part B.quiet=c:= Switch.sunset _ hh z () hX
  by_cases hk:i=B.quiet; · rw [hk,hz,if_pos rfl]; simp [Poly.bead]
  rw [if_neg hk]; simp [Poly.bead,hk]
end YM.LocalTaylorR2.Orbit
