import YM.FVAAlt2.Convert.Cane
/-!
# Engineering rescaling of an MS physical correlation

Hold its drawing fields at fixed renormalization scale and **rescale the arguments**.
This derives the two-sided power/log growth directly from continuum propagation/rates and
its dimensional MS slots. Not an assumption that both formal prescriptions have the same
scale flow (indeed avoiding any extra numerical β/γ prerequisites in this comparison).

No high-order contour analyticity argument here, just exact `MoonB` age transform of
these very momentum results and polynomial bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Currency
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane Fleet Dial
open Frame
open _root_.YM.FVAAlt2.Home.Profiles
open _root_.YM.MS.Theater
open Puff
open scoped Topology ContDiff Classical
variable {W I:Type} [LinearOrder W]{G:Gauge}{B:Deck G}{M:Land.Booked B}{i:ℝ}
variable (A:MS_Data G M)(X: W→ Rake.Label B) {S:Finset W}{q:Geo I} {f:Position W I}
local notation "Gz" => Rake.Label.h ∘ X
lemma isBlip{U:Dance G I W}(hp:DOrd M q A X f U)(i:I)(hf:Injective (pointI f i))(n:ℕ): book A X (q.η i) (pointI f i) S n=blade (U S n) i:= by
 obtain he:= Dial.valid_copy X hp (fun _ : Unit=> i) (Q:=frameF Unit _) (fun _=>rfl); obtain ht: spine A X (q.η i) (pointI f i)=_:= Rake.perfect ( Dial.pin A X (q.η i) hf ) he; unfold Dial.book; rw [ht]; rfl
lemma scale_cost {U:Dance G I W} (h:Mesh q f)(hp:DOrd M q A X f U)(he:S.Nonempty)(i:I)(v:ℝ)(hs: q.η i=v)(hf:Injective (pointI f i))(n:ℕ) (a:ℝ) : Dial.book A X (v-a) ((exp a) • pointI f i) S n=Port.τ (- ( ( Vane.charge Gz S ):ℤ ) ) a*blade (U S n) i:= by
 let d(w:W) (_:Unit):= exp a • f w i; let q':Geo Unit:=frameF Unit v; let p':Geo Unit:=frameF Unit (v-a); let z :Unit→ℝ:=fun _=>a; let F:=pointI f i; let T:= (exp a) • F
 have hh:Injective T:=fun x y hx=> hf ( smul_right_injective (QP) (exp_ne_zero a) hx )
 let Y:= Dial.copy (fun _ : Unit=> i) U; have hz: DOrd M q' A X (fun w _=>f w i) Y:= Dial.valid_copy X hp (fun _=>i) (fun _=> hs.symm )
 have hK:DOrd M p' A X (Port.moved z (fun w _=> f w i)) ( Dial.spine A X (v-a) T ):= Dial.pin A X (v-a) hh
 exact congr_fun ( Port.MoonB A (fun _ : Unit=>Eq.symm (show _=v from Eq.trans (sub_add_cancel v a) rfl)) hz hK S n (fun _=> ( Dial.reports X h hp he n ).1 i) ) () -- shape

variable {d k:ℕ}{K:Set (Points d)}(μ:ℝ)
omit X
-- geometry independent of t; dilate Eta and apply Arch one observer.
structure Shelf (K:Set (Points d)) where
 scale : ℝ
 pose : Points d
 sep : pose∈K
local notation "Σ'"=> Shelf K
abbrev shell(μ:ℝ): Geo (Shelf K):= ⟨0,fun i=> μ+i.scale,fun _=> le_rfl ⟩
abbrev ηX (i:Fin d)(p:Σ'):= realize p.pose i
lemma shelfSpace (hK:IsCompact K)(h:K⊆conf d): Mesh (shell (K:=K) μ) ηX:= by
    intro i j he; let c(x:Points d):= ‖realize x i-realize x j‖; have hc:Continuous c:=by unfold c; fun_prop
    obtain ⟨m,hm⟩:=(hK.image hc).bddAbove
    have hz:∃ a:ℝ,0<a∧∀ x∈K,a≤ c x:= by
      cases Set.eq_empty_or_nonempty K with
      | inl h=> exact ⟨1,zero_lt_one,fun x he=> (Set.notMem_empty x ( h ▸ he )).elim⟩
      | inr hx=> obtain ⟨x,hx,ht⟩:= hK.exists_isMinOn hx hc.continuousOn; exact ⟨ c x,norm_pos_iff.mpr (sub_ne_zero.mpr ((realize_one (h hx)).ne he)),ht⟩
    have hv(x:Σ'): ‖( ηX (K:=K) i - ηX (K:=K) j ) x‖= c x.pose:=rfl
    obtain ⟨a,ha,hq⟩:=hz; set b:=1+max 0 m; have hb:0<b:=by unfold b; linarith [le_max_left 0 m]
    refine ⟨⟨ b,hb,fun x=>?_⟩,⟨ a,ha,fun x=>?_⟩⟩ <;> rw [hv x] <;> simp only [ shell,roots,Pi.zero_apply,exp_zero, mul_one ]
    · exact le_trans (hm ( Set.mem_image_of_mem c x.sep )) (by unfold b; linarith [le_max_right 0 m])
    exact hq _ x.sep

def moving (h:ℕ)(s:ℝ):ℝ:= exp s ^ h
lemma moving_pos (h:ℕ)(s:ℝ):0< moving h s:=by unfold moving; positivity
lemma any_move (c:ℕ)(t:ℝ): Port.τ (-(c:ℤ) ) t=(↑(moving c t)⁻¹:ℂ) := by rw [Port.τ,moving,zpow_neg,zpow_natCast]
variable (P:Fin d→ Rake.Label B)
local notation "sL"=> Vane.charge ( Rake.Label.h∘ P )
abbrev cure (F:Finset (Fin d))(n:ℕ)(x:Σ'):= book A P μ (exp x.scale • realize x.pose) F n
def LowW (μ:ℝ)(F:Shelf K→ ℂ): Prop:= ∃ C:ℝ, 0≤ C ∧ ∃ k:ℕ,∀ i:Shelf K, ‖F i‖≤ C*(1+|μ+i.scale|)^k
lemma cumulants (hK:IsCompact K)(hk:K⊆conf d)(s:Finset (Fin d))(n:ℕ): LowW μ (K:=K) (fun i:Shelf K=> moving (sL s) i.scale • cure A μ P s n i):=by
 have h:= shelfSpace μ hK hk; obtain ⟨U,hu⟩:= Vane.formal (Rake.builder A h P); by_cases hv:s.Nonempty; swap
 · obtain rfl : s=∅:= Finset.not_nonempty_iff_eq_empty.mp hv; refine ⟨0,le_rfl,0,fun i=>?_⟩; let x:= realize i.pose; let f:Fin d→QP:=exp i.scale • x; have he:Injective f:= fun a b hx=> realize_one (hk i.sep) (smul_right_injective QP (exp_ne_zero _) hx); unfold cure Dial.book; change ‖_ • blade (spine A P μ f ∅ n) ()‖ ≤ _; rw [show spine A P μ f ∅=0 from (pin A P μ he).1]; simp [ (Fleet.allow_zero (G:=G) ()).2 ]
 obtain ⟨C,hC,k,hX⟩:= Dial.reports P h hu hv n|>.2.2; refine ⟨ C,hC.le,k,fun i=>?_⟩; let b:= μ+i.scale; let f:= realize i.pose; have hq: Injective f:=realize_one (hk i.sep)
 have he : cure A μ P s n i=(Port.τ (-(sL s:ℤ)) i.scale)*blade (U s n) i := by obtain he := scale_cost A P h hu hv i b rfl hq n i.scale; rw [show b-i.scale=μ from add_sub_cancel_right .. ] at he; exact he
 change ‖moving _ _ • cure A μ P s n i‖ ≤ _; rw [he,any_move, show ( moving (sL s) i.scale ) • _ = blade (U s n) i from ?_ ]; rotate_left; · simp_rw [ Complex.real_smul ]; rw [ Complex.ofReal_inv,mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (moving_pos ..|>.ne'))]
 apply (hX i).trans_eq; unfold moneyX tarB habitat shell; simp
end YM.MS.FVA.Currency
