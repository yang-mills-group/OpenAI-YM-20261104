import YM.OPE.Levy.Invoice
/-! # Stronger coupled receipt on the weak-station supplier -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Function Filter Set RG Marker Next.Extract Dash Cells MeasureTheory Lattice Wilson Source Extra.Histories
open Spec MergeProof Org MergeProof.East Next.Rank Next.Rank.Price Precision Next.Rank.East
open Next.Rank.Ribbon Next.Rank.Tapes.West Perch Atlas Next.Rank.Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Extraction Bid Further.CorrectedLift
open PhysicalNext.RankCovariance PhysicalNext.Repeat.Legato.Bandage
open Next.UVStress Climb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

lemma regraduate {P E:Type*}[Norm E]{l:Filter P}
   {X Y:P→ℝ}{f:P→E}{a:ℝ}(ht:Tendsto Y l atTop)(hxy:Tendsto (fun i=>X i/Y i) l (𝓝 1))(hf:RateLE l X f a): RateLE l Y f a:= by
    intro r hr
    obtain ⟨s,hs,hs'⟩:= exists_between hr
    filter_upwards [(hxy.const_mul s).eventually (gt_mem_nhds (by rwa [mul_one])), hf s hs, ht.eventually_gt_atTop 0] with i hi h₁ h₂
    exact h₁.trans (Real.exp_monotone ((div_le_iff₀ h₂).mp (show (s*X i)/Y i ≤ r from by rw [mul_div_assoc]; exact hi.le)))

variable {G:Gauge} {C:Family G} {F:Extraction.Order} {D d i N n p:ℕ} {ι:Type}[Fintype ι] {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "A" => C.path.levels
local notation "S"=> standard C
local notation "T₀" => C.S.scale

def rents (U:ℕ→Wheel C D)(i:ℕ) := -Real.log (U i).r
def Lodged (F:Extraction.Order)(U:ℕ→Wheel C D) : Prop := ∃ (k:ℕ→ℕ), ∃ (c: Fin (D+1)→ℕ→ℝ), Tendsto (rents U) atTop atTop ∧ Tendsto (fun i=> T₀ (k i) / rents U i) atTop (𝓝 1) ∧
  Tendsto k atTop atTop ∧
  (∀ d : Fin (D+1),RateLE atTop (rents U) (c d) (-(d:ℝ))) ∧ (∀ (d:Fin (D+1)) i,∀ᶠ l in F.fuse, ∀ v, Next.UVStress.quota C d.val (k i) l.1 l.2 ((U i).toStation.atCut l d v) ≤ c d i * ‖v‖) ∧
   ∀ (d:Fin (D+1)) i,C.ref d ≤ k i
def Stocked (C:Family G)(F:Extraction.Order):Prop :=∀ (n d:ℕ)(r:ℝ),(standard C).Smooth → ∀ h:(standard C).RealSpin, 0 < r → ∃ U:ℕ→ Wheel C d, Granular U F h n r ∧ Lodged (F:=F) U

variable (C)
lemma mag_price (b:ℝ)(hG:G.Simple):RateIs atTop T₀ (Station.mag A b) 0:=by
    let q i:=Station.mag A (-b) i
    let z k:=Station.mag A b k
    have hs(k):q k*z k=1:= by change _^(-b)*_^b=1; rw [←Real.rpow_add (show 0 < (A).clock.monitor k from Real.exp_pos _),neg_add_cancel,Real.rpow_zero]
    refine ⟨Eventually.of_forall fun k=> Station.mag_pos .., tendsto_order.mpr ⟨fun r hr=> ?_, fun r hr=> ?_⟩⟩
    · have hh:(0:ℝ) < -r/2:=half_pos (neg_pos.mpr hr)
      filter_upwards [Tendsto.eventually_gt_atTop (C.S.divergent) 0,station_monitor C hG (-b) (-r/2) hh] with i ht hx
      have hq:0 < q i:=Station.mag_pos ..;have hy:0 < z i:=Station.mag_pos ..
      change r < Real.log (z i)/T₀ i
      have he:=Real.log_mul hq.ne' hy.ne'; rw [hs i,Real.log_one] at he
      rw [lt_div_iff₀ ht]; change ‖q i‖ ≤ _ at hx; rw [Real.norm_of_nonneg hq.le] at hx; have hl:Real.log (q i)≤_ := (Real.log_le_iff_le_exp hq).2 hx
      nlinarith only [neg_neg_of_pos ht,hl,he,hh,hr]
    have hh:(0:ℝ) < r/2:=half_pos hr
    filter_upwards [Tendsto.eventually_gt_atTop (C.S.divergent) 0, station_monitor C hG b (r/2) hh] with i ht hx
    have hp:0 < z i:=Station.mag_pos ..
    change ‖z i‖ ≤ _ at hx; change Real.log (z i)/T₀ i<r
    rw [Real.norm_of_nonneg hp.le] at hx; exact (div_lt_iff₀ ht).mpr (lt_of_le_of_lt ((Real.log_le_iff_le_exp hp).2 hx) (mul_lt_mul_of_pos_right (by linarith) ht))

lemma take_rents (g:G.Simple)(c:ℝ) :
      let Y:=fun i=>-Real.log (gap A c i)
      Tendsto Y atTop atTop ∧ Tendsto (fun i=> T₀ i/ Y i) atTop (𝓝 1):=by
    intro Y
    have ht:(fun k=> Y k)=fun k=>T₀ k-Real.log (mag A c k):=funext fun i=>by dsimp only [Y]; change -Real.log (C.S.a _ * mag A c i)=_; rw [Real.log_mul (C.S.a_pos i).ne' (Station.mag_pos ..).ne',Stock.a_log, Real.log_exp]; ring
    have h:Tendsto (fun k=>Y k/T₀ k) atTop (𝓝 1):=by
      have he:= (mag_price C c g).rate.const_sub 1
      rw [sub_zero] at he
      refine he.congr' ?_
      filter_upwards [C.S.divergent.eventually_gt_atTop 0] with i hi; rw [show Y i= _ from congr_fun ht i,sub_div,div_self hi.ne']
    refine ⟨tendsto_atTop_mono' _ ?_ (Tendsto.const_mul_atTop (r:=(1/2:ℝ)) (by norm_num) C.S.divergent),?_⟩
    · filter_upwards [h.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num)), C.S.divergent.eventually_gt_atTop 0] with i hi ht; exact ((lt_div_iff₀ ht).mp hi).le
    simpa [inv_div] using h.inv₀ (one_ne_zero' ℝ)

variable {C} (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(g:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}

include g hp H hZ
-- adaptation of Largo.podium
lemma receipt (hn:2≤n)(R:ℝ)(hr:0<R)(hs:(S).Smooth)(H':(S).RealSpin) (hg:Checks (P x).arc (P y).arc (P w).arc c n D)
   (hw:∃ᶠ k in atTop,∃ Y,Poised P B H O J n z k Y) : ∃ W', Granular (D:=D) W' F H' n R ∧ Lodged (F:=F) W':=by
   obtain ⟨f,hf,hh⟩:= extraction_of_frequently_atTop hw; choose Y hY using hh
   let a:= (P x).arc;let K:= fun i=>wok C D (f i) a c (Y i); have hx(i):= w_right c F H' a (hY i)
   have he := hf.tendsto_atTop
   refine ⟨K,⟨⟨Eventually.of_forall (fun i=>(hx i).1),?_,?_,?_⟩,(Station.gap_rate A g a).comp he,fun m hm t ht w=> aspect P B H g hp O J z hZ F hn R hr hs H' hg t ht (depthWord t w) hm he Y hY⟩,?_⟩
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.2
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
lemma shrink_witness {D M k' k:ℕ} {R:ℝ} (W:ℕ→Wheel C D) (H:(S).RealSpin)(F:Extraction.Order)(h:Granular W F H k R)(hd:M≤D)(hk:k' ≤ k)(hh:Lodged (F:=F) W): ∃ V, Granular (D:=M) V F H k' R ∧ Lodged (F:=F) V:=by
    let f(x : Fin (M+1)):Fin (D+1):=⟨x,(Nat.lt_of_lt_of_le x.isLt (Nat.add_le_add_right hd 1))⟩; let V:ℕ→ Wheel C M:= fun i=> {r:=(W i).r,rad:=(W i).rad, grid:=(W i).grid, σ:=(W i).σ,stripe:=(W i).stripe,atCut:=fun z x=>(W i).atCut z (f x)}
    obtain ⟨v,f₀,h₁,h₂,h0,h₃,h₄,h₅⟩:=hh
    refine ⟨V, ⟨⟨h.grants.mono (fun i hk=> ?_), h.central,h.real.mono (fun i hi=> hi.mono fun j hj=>hj.mono fun k hk u=> hk (f u)),h.h_symm.mono (fun i hi=> hi.mono fun j hj=>hj.mono fun k hk u=> hk (f u))⟩,h.small,?_⟩,v,f₀ ∘ f,h₁,h₂,h0,fun d=>h₃ (f d),fun d i=>h₄ (f d) i,fun d i=>h₅ (f d) i⟩
    · obtain ⟨a,hA⟩:= hk; refine ⟨max a 0,hA.mono fun i hi=>hi.mono fun j hj=> (pi_norm_le_iff_of_nonneg (le_max_right ..)).2 (fun k=> (norm_le_pi_norm (W _|>.atCut _) (f k)).trans (hj.trans (le_max_left ..)))⟩
    intro n hn t hu x
    obtain ⟨e,a,b,hB⟩:= h.proof_ n (hn.trans hk) t (fun i=>(hu i).trans hd) x
    refine ⟨e,a,b,hB.goes,hB.stripe,hB.room,hB.pos,hB.off,hB.on_,hB.costs.mono fun i hi=>?_⟩
    exact ⟨hi.compare,hi.crude,hi.slab⟩
end YM.OPE.Levy
