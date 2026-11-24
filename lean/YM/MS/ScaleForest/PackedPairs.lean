import YM.MS.ScaleForest.WirePinned
/-!
# The same scale and meromorphic z-rules after gluing both branches to positions

First at fixed log length. In particular these facts treat all axes carried
by the source tensor AND the integration with dimensional gluing kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Fiddle
open scoped Topology ContDiff
variable {G : Gauge} {z : ℂ} {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b ξ ε : I → ℝ}
   {K : Rip G} {F H : I→ Mob G} {X Y : Mob G} {p s : ℤ} {L : Set ℂ} {U V : ℂ→ Mob G} {r : ℝ}
   {Z : I→ℂ} {v : I→ℝ} {P : I→QP} {n : ℕ}

section
variable (h : Knot false K) (hw : closedF K false) (hr : reverseF K) (hx : Form0 false X) (hy : Form0 false Y)
include h hx hy

theorem swept_forms (hp : z∈Town) : Form0 false (sweptRef z K X Y) :=
   ((torn hp (form_weave hx hy) h).sub (form_weave (torn hp hx h) hy)).sub (form_weave hx (torn hp hy h))
omit h hx hy
theorem weave_goods (hp : Goods p X) (hs : Goods s Y) : Goods (p+s) (weave X Y) := fun m=> Rails.product (hp m) (hs m)
include h hx hy hw hr
variable (hp : z∈Town)
include hp

theorem placed_forms (A:QP) (y : ℝ) : Form0 false (pinned K z y A X Y) := placedEq h hw hr hx hy hp A y |>.symm ▸ (swept_forms h (form_rephase hx _) hy hp).smul _
theorem placed_goods (he : Goods p X) (hg : Goods s Y) (A:QP) (y : ℝ) : Goods (p+s-2) (pinned K z y A X Y) := by
   rw [placedEq h hw hr hx hy hp]; let Q:= good (p+s-2) G; have ht : Goods p (rephase A X) := fun m i hi=> by rw [rephase_test,he m i hi, mul_zero]
   have h_A:= form_rephase hx A
   refine Q.smul_mem _ (Q.sub_mem (Q.sub_mem (goods_o (form_weave h_A hy) h hp (weave_goods ht hg))
      (?_ : Goods (p+s-2) _)) (?_ : Goods (p+s-2) _))
   · rw [show p+s-2=p-2+s by omega]; exact weave_goods (goods_o h_A h hp ht) hg
   rw [add_sub_assoc]; exact weave_goods ht (goods_o hy h hp hg)

-- scale all momentum arguments simultaneously
omit h hx hy hw hr hp in
theorem weave_shift (X Y : Mob G) (t : ℝ) (a b : ℂ) : weave (plow a t X) (plow b t Y)=plow (a+b) t (weave X Y) := by
   funext m l; unfold plow weave; simp only [scattered,scatter_sr];
   refine Eq.trans ?_ (map_smul (allocate (field parity) l) (amount (a+b+(mass l:ℂ)) t) (fun p q=> X m (sr t p)*Y m (sr t q)));
   refine scatter_congr _ _ _ _ (fun p q hp=>?_); simp only [Pi.smul_apply,smul_eq_mul]
   rw [← price_mag_split hp,Int.cast_add]; simp only [amount_add]; ring
omit h hx hy hw hr hp in
theorem phase_shift (t : ℝ) (X : Mob G) (A : QP) (a : ℂ) : rephase A (plow a t X)= plow a t (rephase (exp (-t) • A) X) := by
   funext m l; unfold plow; simp only [rephase_test,waveFact,net_sr,map_smul]
   rw [Tone.Mesh.dual, smul_smul, Real.exp_neg, mul_inv_cancel₀ (Real.exp_pos t).ne',one_smul]; ring

omit hp hw hr in
theorem swept_shift (t : ℝ) (z a b : ℂ) : sweptRef z (pulse 4 t K) (plow a t X) (plow b t Y)=plow (a+b+(-2*z)) t (sweptRef z K X Y) := by
   unfold sweptRef
   rw [weave_shift, air_ocean (form_weave hx hy).price h.price,
     air_ocean hx.price h.price, air_ocean hy.price h.price, weave_shift,weave_shift];
   rw [show 4+(a+b)-4-2*z=a+b+ -2*z from by ring, show 4+a-4-2*z+b=a+b+ -2*z from by ring, show a+(4+b-4-2*z)=a+b+ -2*z from by ring];
   simp_rw [← cert,map_sub]
omit h hx hy hw hr hp in
theorem μ_shift (t y : ℝ) (z : ℂ) : tenorK z (y+t)= tenorK z y * amount (-2*z) t := by
   rw [restore_tape,restore_tape,mul_assoc (feeD _), amount,← Complex.exp_add]; push_cast; ring_nf
omit h hx hy hr hp in
theorem pulsed_closed (t : ℝ) : closedF (pulse 4 t K) false := fun m i j p h=> hw m i j (exp t • p) (fun q=> h (by simp [Alps.pulse,q]))

theorem pinned_meter (t y : ℝ) (a b : ℂ) (A:QP) : pinned (pulse 4 t K) z y A (plow a t X) (plow b t Y) = plow (a+b) t (pinned K z (y+t) (exp (-t) • A) X Y) := by
   rw [placedEq (fze h _ _) (pulsed_closed hw t) (a_rev t 4 hr) (fseed hx a t) (fseed hy b t) hp,
     phase_shift,swept_shift h (form_rephase hx _) hy,
     placedEq h hw hr hx hy hp, μ_shift, Alps.shift (a+b) (-2*z)]; simp_rw [← cert,map_smul,mul_smul]

omit hy hp hw hr in
theorem closure_meter (t y : ℝ) (z a : ℂ) : closeG (pulse 4 t K) z y (plow a t X) = plow a t (closeG K z (y+t) X) := by
   rw [closeG_eq,closeG_eq,μ_shift, air_ocean hx.price h.price,show 4+a-4-2*z= a+ -2*z from by ring,
     Alps.shift a (-2*z)]; simp_rw [← cert,map_smul,mul_smul]
end

section
variable (h : Knot false K) (hx : ∀ i,Sturdy false (F i)) (hy : ∀ i,Sturdy false (H i))
   (hF : fell ξ a F) (hH : fell ξ b H) (hw : ∀ i, Z i∈Town) (ht : ∀ i, ‖Z i‖≤(n : ℝ))
   (hp : scaleC ξ ε (fun i=> ‖tenorK (Z i) (v i)‖))
include h hx hF hw ht
omit h hx hF hw in
private theorem sc_test (m : ℕ) : scaleC ξ 1 (fun i=> ‖2*(Z i-m)‖) := by
   let h:= 1+2*((n:ℝ)+m); refine ⟨h,(by unfold h; positivity),0,fun i _ _=>?_⟩
   have hm:= (norm_sub_le (Z i) (m:ℂ)).trans (add_le_add_left (ht i) _); simp at hm
   simp only [ pow_zero,mul_one,Pi.one_apply,h,Complex.norm_two,norm_mul ]
   linarith
omit h hx hF hw in
private theorem ups_test (i:I) : 2*(Z i).re+1≤ ((2*n+1:ℕ):ℝ) := by have hg:= (Complex.re_le_norm _).trans (ht i); push_cast; linarith

theorem costOcean : fell ξ a (fun i=> ocean (Z i) K (F i)) := by
   convert! regular_fin (fun n=> sc_test ht n) hF (transport h.price) hw (ups_test ht) hx (fun _=> h.token) (fun _=>zero_le_one) using 1; simp
include hy hH

theorem costSweep : fell ξ (a*b) (fun i=> sweptRef (Z i) K (F i) (H i)) :=
   fall_sub (fall_sub (costOcean h (fun i=> weave_token (hx i) (hy i)) (weave_price hF hH) hw ht) (weave_price (costOcean h hx hF hw ht) hH)) (weave_price hF (costOcean h hy hH hw ht))
include hp

theorem costPinn (he : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (Arc.path ξ).full.Le (fun i (_:E)=>‖P i‖) (fun _ _=>1)) (hc : closedF K false) (hr : reverseF K) :
    fell ξ (ε*(a*b)) (fun i=> pinned K (Z i) (v i) (P i) (F i) (H i)) := by
   simp_rw [placedEq h hc hr (Form0.mk (fee hF _) (hx _)) (Form0.mk (fee hH _) (hy _)) (hw _)];
   exact fall_scale (costSweep h (fun i=> rephase_token (P i) (hx i)) hy (rephase_price hF he) hH hw ht) hp
omit hy hH in
theorem costClose : fell ξ (ε*a) (fun i=> closeG K (Z i) (v i) (F i)) := by
   simp_rw [closeG_eq]; exact fall_scale (costOcean h hx hF hw ht) hp
end

section
variable (h : Knot false K) (hx : Hol L U) (hy : Hol L V) (hw : L⊆Town) (ht : IsOpen L) (hU : ∀ i∈L,Sturdy false (U i)) (hV : ∀ i∈L,Sturdy false (V i))
include hw
theorem holFee (y : ℝ) : Forest L (fun i : ℂ=> tenorK i y) := by
   simp_rw [restore_tape]; exact fun i hi=> DifferentiableAt.mul (fee_H i (hw hi)) (by fun_prop)
include h hx hU ht
theorem holClose (y : ℝ) : Hol L (fun i=> closeG K i y (U i)) := by simp_rw [closeG_eq]; exact Hol.rate (wind_he hx (Hop.crate h.price) hw hU (fun _ _=> h.token) ht) (holFee hw _)
include hy hV

theorem holSweep : Hol L (fun i=> sweptRef i K (U i) (V i)) := by
   exact Hol.sub (Hol.sub (wind_he (hol_weave hx hy) (Hop.crate h.price) hw (fun i hi=> weave_token (hU i hi) (hV i hi)) (fun _ _=> h.token) ht)
      (hol_weave (wind_he hx (Hop.crate h.price) hw hU (fun _ _=>h.token) ht) hy)) (hol_weave hx (wind_he hy (Hop.crate h.price) hw hV (fun _ _=> h.token) ht))

theorem holPinned (hc : closedF K false) (hr : reverseF K) (y : ℝ) (A:QP) :
    Hol L (fun i=> pinned K i y A (U i) (V i)) := by
   refine Hol.con (Hol.rate (holSweep h (hol_rephase hx A) hy hw ht (fun i hi=> rephase_token _ (hU i hi)) hV) (holFee hw y)) ht (fun i hi=>?_)
   exact (placedEq h hc hr ⟨hx.link hi ht,hU i hi⟩ ⟨hy.link hi ht,hV i hi⟩ (hw hi) A y).symm
end
end YM.MS.ScaleForest
