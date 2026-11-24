import YM.OPE.Levy.Lodging
import YM.OPE.Coverage.Sampling

/-! # Weak columns on enough stations for every demand, retaining the mesh neighborhood

Adaptation of Levy.receipt/shrink_witness with the exact same formulas and
charges. Widths before the measurement hop are bought on same-stage data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Levy PhysicalNext.InteractingRank.Soft
open Function Filter Set RG Marker Next.Extract Dash Cells MeasureTheory Lattice Wilson Source Extra.Histories
open Spec MergeProof Org MergeProof.East Next.Rank Next.Rank.Price Precision Next.Rank.East
open Next.Rank.Ribbon Next.Rank.Tapes.West Perch Atlas Next.Rank.Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Extraction Bid Further.CorrectedLift
open PhysicalNext.RankCovariance PhysicalNext.Repeat.Legato.Bandage
open Next.UVStress Climb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical


variable {G:Gauge} {C:Family G} {F:Extraction.Order} {D d i N n p:ℕ} {ι:Type}[Fintype ι] {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "A" => C.path.levels
local notation "S"=> standard C
local notation "T₀" => C.S.scale


abbrev WheelNear (U:ℕ→Wheel C D):= LogNear C.path.levels (fun i=>(U i).r)
structure Stripe (U : ℕ → Wheel C D):Prop where
  rate : ∀ p:ℝ,p>0 → ∀ᶠ i:ℕ in atTop, (U i).σ⁻¹ ≤ (1+rents U i)^p
structure Paved (C:Family G)(F:Extraction.Order):Prop where
 stride : ∀ᶠ i:ℕ in atTop,Real.log ((C.S.block i).val:ℝ) ≤ Real.log (1+C.S.scale (i+1))
 demand : ∀ (n d:ℕ)(r:ℝ),(standard C).Smooth → ∀ h:(standard C).RealSpin, 0 < r → ∃ U:ℕ→ Wheel C d, Granular U F h n r ∧ Lodged (F:=F) U ∧ WheelNear U ∧ Stripe U
lemma Paved.stocked (h:Paved C F):Stocked C F:=by
   intro n d r hs hF hr; obtain ⟨U,h1,h2,-,-⟩:= h.demand n d r hs hF hr
   exact ⟨U,h1,h2⟩
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(g:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}

lemma stripe_wok(C:Family G) (a:ℝ){q:ℕ→ℕ}(hq:Tendsto q atTop atTop)(Y:ℕ→ℕ→ℕ→TableL C D) (g:G.Simple) : Stripe (fun i=>wok C D (q i) a c (Y i)):=by
  let k:= fun i=>wok C D (q i) a c (Y i)
  let u:= k
  have hu:= take_rents C g a
  let v:= fun i =>C.path.levels.clock.hatBeta (q i)
  have he : Tendsto (fun i=>v i/rents u i) atTop (𝓝 G.slopeConstant):=by
    let AA:=C.path.levels
    have hh:= (tendsto_const_nhds (f:=atTop) (x:=AA.clock.bar) |>.div_atTop hu.1).add (hu.2.const_mul G.slopeConstant)
    rw [zero_add,mul_one] at hh
    apply (Tendsto.comp (g:=fun j=>AA.clock.hatBeta j/(-Real.log (gap AA a j))) (f:=q) ?_ hq)
    exact (hh.congr fun i=> (by change AA.clock.bar / _ + G.slopeConstant * (_ / _)=_; change _ = AA.clock.hatBeta i/ -_ ; unfold Calendar.hatBeta; ring))
  constructor; intro p hp
  have hz : Tendsto v atTop atTop:= (hat_rate C.path.levels g).comp hq
  filter_upwards [hz.eventually (Vac.Numbers.cost (-c) (p/2) (half_pos hp)),he.eventually (gt_mem_nhds (by linarith only : G.slopeConstant < G.slopeConstant + 1)), (hu.1.comp hq).eventually_gt_atTop (G.slopeConstant+1),hz.eventually_gt_atTop 0] with i hi hx hv hg
  change v i / rents u i < G.slopeConstant +1 at hx
  change G.slopeConstant + 1 < rents u i at hv
  have ht:= div_lt_iff₀ ((add_pos (Gauge.slopeConstant_pos g) one_pos).trans hv) |>.mp hx
  have h1: Vac.Numbers.P (v i)^(-c)=(u i).σ⁻¹:=by
      nth_rw 1 [← Real.exp_log (show 0 < Vac.Numbers.P (v i) from Real.exp_pos _)]; rw [← Real.exp_mul]; unfold Vac.Numbers.P; rw [Real.log_exp]; dsimp only [u,k,wok]
      unfold Perch.bill Perch.boil Perch.y
      rw [← Real.exp_neg]; congr 1; ring
  calc _ ≤ (v i)^(p/2) := h1 ▸ hi
       _ ≤ ((1+rents u i)^2)^(p/2) := Real.rpow_le_rpow hg.le (by nlinarith only [ht,hv, Gauge.slopeConstant_pos g]) (half_pos hp).le
       _ = _ :=?_ -- combine powers
  rw [(show ((1+rents u i):ℝ)^2=(1+rents u i)^(2:ℝ) from by norm_cast),← Real.rpow_mul (by nlinarith only [hv,Gauge.slopeConstant_pos g])]; congr; ring
include g hp H hZ
-- adaptation of Largo.podium
lemma frontage (hn:2≤n)(R:ℝ)(hr:0<R)(hs:(S).Smooth)(H':(S).RealSpin) (hg:Checks (P x).arc (P y).arc (P w).arc c n D)
   (q₀:ℕ→ℕ)(ht₀:Tendsto q₀ atTop atTop)(hw:∀ᶠ k in atTop,∃ Y,Poised P B H O J n z (q₀ k) Y)(hl:LogNear C.path.levels (gap C.path.levels (P x).arc ∘ q₀)) : ∃ W', Granular (D:=D) W' F H' n R ∧ Lodged (F:=F) W' ∧ WheelNear W' ∧ Stripe W':=by
   obtain ⟨M,hM⟩:= eventually_atTop.mp hw
   let idx (i:ℕ):= max M i
   let f:=q₀ ∘ idx
   have hs':idx=ᶠ[atTop] id := (eventually_ge_atTop M).mono (fun i hi=>max_eq_right hi)
   choose Y hY using fun i=> hM (idx i) (le_max_left ..)
   let a:= (P x).arc;let K:= fun i=>wok C D (f i) a c (Y i); have hx(i):= w_right c F H' a (hY i)
   have he := ht₀.comp (tendsto_atTop_mono (f:=id) (g:=idx) (fun i=>le_max_right ..) tendsto_id)
   refine ⟨K,⟨⟨Eventually.of_forall (fun i=>(hx i).1),?_,?_,?_⟩,(Station.gap_rate A g a).comp he,fun m hm t ht w=> aspect P B H g hp O J z hZ F hn R hr hs H' hg t ht (depthWord t w) hm he Y hY⟩,?_,?_,?_⟩
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.2
   rotate_left
   · obtain ⟨e,he,-,hl⟩:=hl
     refine ⟨e,he,fun i=>(K i).rad,?_⟩
     filter_upwards [hs',hl] with i hi hl
     change |Real.log ((gap A (P x).arc ∘ q₀) (idx i)) + T₀ i| ≤ _
     exact (show idx i=i from hi).symm ▸ hl
   · exact stripe_wok (D:=D) (c:=c) C a he Y g
   let t(d:Fin (D+1))(i:ℕ):= signal C d (f i) a * ‖ladder C d‖
   obtain ⟨ht,htu⟩:= take_rents C g a
   refine ⟨f,t,ht.comp he,htu.comp he, he, fun d=> ?_, fun d i=> ?_, fun d i=> (hY i).early d.val (Nat.le_of_lt_succ d.isLt)⟩
   · have hh := ((signal_rate C d a g).mul (RateLE.const ‖ladder C d‖ C.S.divergent)).comp he
     have hTi:=htu.comp he
     have hroot: (rents K)=( (fun i=>-Real.log (gap A a i)) ∘ f) :=rfl
     rw [hroot]
     rw [add_zero] at hh; exact regraduate (ht.comp he) hTi hh
   filter_upwards [Tendsto.eventually_gt_atTop (Push.RelayDifference.cutoff_grows F) (f i)] with j hj v
   let U:=ladder C d
   have hd:= (show (d:ℕ) ≤D from Nat.le_of_lt_succ d.isLt)
   have hk:= quotation C (N:=j.1) (p:=j.2) (d:ℕ) (f i) (b:=a) H ((hY i).early _ hd) hj.le ((Y i j.1 j.2 d)) ((hY i).charts j.1 j.2 hj d).1 ((U v):C.label d)
   change Next.UVStress.quota C _ _ _ _ ((ladd C (mag A a (f i)) ..) (U v)) ≤ _*‖U v‖ at hk
   refine le_trans (b:= signal C d (f i) a * ‖U v‖) ?_ ?_
   · exact hk
   unfold t; rw [mul_assoc]
   exact mul_le_mul_of_nonneg_left (U.le_opNorm _) (mul_nonneg (pow_nonneg (C.S.a_pos _).le _) (mul_nonneg zero_le_two (Finset.sum_nonneg fun x y=>norm_nonneg _)))

omit hp g H hZ in
lemma reduce_near {D M k' k:ℕ} {R:ℝ} (W:ℕ→Wheel C D) (H:(S).RealSpin)(F:Extraction.Order)(h:Granular W F H k R)(hd:M≤D)(hk:k' ≤ k)(hh:Lodged (F:=F) W)(hw:WheelNear W) (he:Stripe W): ∃ V, Granular (D:=M) V F H k' R ∧ Lodged (F:=F) V ∧ WheelNear V ∧ Stripe V:=by
    let f(x : Fin (M+1)):Fin (D+1):=⟨x,(Nat.lt_of_lt_of_le x.isLt (Nat.add_le_add_right hd 1))⟩; let V:ℕ→ Wheel C M:= fun i=> {r:=(W i).r,rad:=(W i).rad, grid:=(W i).grid, σ:=(W i).σ,stripe:=(W i).stripe,atCut:=fun z x=>(W i).atCut z (f x)}
    obtain ⟨v,f₀,h₁,h₂,h0,h₃,h₄,h₅⟩:=hh
    refine ⟨V, ⟨⟨h.grants.mono (fun i hk=> ?_), h.central,h.real.mono (fun i hi=> hi.mono fun j hj=>hj.mono fun k hk u=> hk (f u)),h.h_symm.mono (fun i hi=> hi.mono fun j hj=>hj.mono fun k hk u=> hk (f u))⟩,h.small,?_⟩,⟨v,f₀ ∘ f,h₁,h₂,h0,fun d=>h₃ (f d),fun d i=>h₄ (f d) i,fun d i=>h₅ (f d) i⟩, hw, ?_⟩
    · obtain ⟨a,hA⟩:= hk; refine ⟨max a 0,hA.mono fun i hi=>hi.mono fun j hj=> (pi_norm_le_iff_of_nonneg (le_max_right ..)).2 (fun k=> (norm_le_pi_norm (W _|>.atCut _) (f k)).trans (hj.trans (le_max_left ..)))⟩
    swap; · exact ⟨he.rate⟩
    intro n hn t hu x
    obtain ⟨e,a,b,hB⟩:= h.proof_ n (hn.trans hk) t (fun i=>(hu i).trans hd) x
    refine ⟨e,a,b,hB.goes,hB.stripe,hB.room,hB.pos,hB.off,hB.on_,hB.costs.mono fun i hi=>?_⟩
    exact ⟨hi.compare,hi.crude,hi.slab⟩
end YM.OPE.Coverage
