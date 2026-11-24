import YM.RG12.Rail.Wind
/-! Adapt top constant shape lemma on cover and portrait to growing separated
  rays. Only shape-facing quantities: reuse ALL calendar estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Set Filter Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Next.Rank.Value
open Glimmer Peak Prayer Configuration Perch Marker Glyph Cells Market Read Dock Camp Beamer Normal
open scoped Topology BigOperators Classical
variable {G:Gauge} {A:Levels G} {n d:ℕ} (H:G.Simple)
variable {a:Points n} (ha:a∈conf n) {b:ℝ} (f:ℕ→ℕ) (hf:Tendsto f atTop atTop) (x:ℕ→Points n)(t:ℕ→ℝ) (ht:∀ i,1 ≤ t i)
  (hc:∀ i,tested A b (f i) (x i)= (t i) • a){u:ℝ}(hu:Tendsto (fun i=>(t i)⁻¹) atTop (𝓝 u))

include H ha hf ht hc hu
lemma covers (l:ℝ)(hl:0<l) (p q:Fin n× KeyIn G d) : ∀ᶠ i in atTop,∀ h:Fit A b (f i) (x i), ‖(currentX (Ship.fitting h) G d).cov p q‖ ≤ (1/2)*bill l (clim A (f i)):=by
    obtain ⟨z,hz⟩:=pair_wind ha p q t ht hu
    filter_upwards [hz.norm.eventually (ge_mem_nhds (lt_add_one (‖z‖))),(((bill_lo hl).comp ((hat_rate A H).comp hf)).const_mul_atTop (by norm_num : 0 < (1/2:ℝ))).eventually_ge_atTop (‖z‖+1)] with k hk hh h
    change ‖readsEach _ _ _ _ _‖ ≤ _; rw [hc]; exact hk.trans hh
-- both ports for anemometer. compare West/Coke and Cream
variable {C:Family G}
lemma clockR (D₀ d:ℕ)(hb:0<b) : ∀ᶠ k in atTop,∀ hp : Fit A b (f k) (x k),
    let s:=clim A (f k)
    Meridian (G:=G) d (Ship.fitting hp) (fraction n D₀ s) (fraction n D₀ s) (bill (-3) s) (bill (fuel D₀ n) s) (bill (-2) s) (Station.mag A b (f k)) (lengthW s) := by
  obtain ⟨c,hc',he⟩ := sense G d; let ζ := fuel D₀ n
  have hp : 0<ζ := fuel_real D₀ n
  have hh : ζ≤1/4 := by dsimp only [ζ,fuel]; apply div_le_div_of_nonneg_left zero_le_one (by norm_num); push_cast;nlinarith
  have hec := (hat_rate A H).comp hf
  have hz := transports (b:=ζ) (a:=3*ζ/4) (by linarith) 2
  filter_upwards [eventually_all.mpr fun i => eventually_all.mpr fun j => covers (d:=d) H ha f hf x t ht hc hu ζ hp i j,
    hec.eventually (zone_power (d-1) (a:=ζ/4) (by linarith)), ( (bill_lo (a:=ζ/4) (by linarith)).comp hec).eventually_ge_atTop c, hec.eventually hz]
    with k H1 H2 H3 H4
  intro hθ s
  have hs : fraction n D₀ s=bill (ζ/4) s := rfl
  let T := fraction n D₀ s; have hT : 1 ≤ T := Glimmer.costed (ζ/4) s (by linarith)
  have hz : 1 ≤ Station.mag A b (f k) := by rw [mag_bill]; exact Glimmer.costed _ _ hb.le
  have hB : T*T*T ≤ (1/2)*bill ζ s := by
    change 2*bill _ s ≤ bill _ s at H4
    rw [show T= _ from hs,overlap,overlap,show ζ/4 + ζ/4 + ζ/4=3*ζ/4 by ring]; linarith only [H4]
  have hC : 0<bill ζ s := Real.exp_pos _
  refine ⟨hz,zero_le_one.trans hT,zero_le_one.trans hT,(Real.exp_pos _).le,Glimmer.costed _ s hp.le, fun i => (he _).trans H3,H2,
    ?_,?_,?_,fun i j => ?_, by linarith only [hB,hC]⟩
  · apply (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hT) (zero_le_one.trans hT)) hT).trans; linarith only [hB,hC]
  · rw [hs, overlap, overlap]; apply billed; linarith only [hh]
  · rw [hs,overlap]; apply billed; linarith only [hh]
  change ‖_‖+T*T*T ≤ bill ζ s; linarith only [show ‖_‖≤(1/2)*bill ζ s from H1 i j hθ,hB]

lemma penR (hb:5≤b) (d:ℕ): ∀ᶠ k in atTop, ∀ hp : Fit A b (f k) (x k), ∀ (i j : Fin n) (L S : Hub G d 0), i ≠ j →
      let T := tested A b (f k) (x k); let r := mag A b (f k)
      ‖amount r L.val * amount r S.val * mourn (gesture L.val) (gesture S.val) (collect d (Ship.fitting hp) r G i j) -
        light L.val S.val (T i) (T j)‖ ≤ bill (-4) (clim A (f k)) := by
  suffices hq : ∀ᶠ k in atTop, ∀ (i j : Fin n) (L S : Hub G d 0), i≠j → ∀ hp : Fit A b (f k) (x k),
      let T := tested A b (f k) (x k); let r := mag A b (f k)
      ‖amount r L.val * amount r S.val * mourn (gesture L.val) (gesture S.val) (collect d (Ship.fitting hp) r G i j) -
        light L.val S.val (T i) (T j)‖ ≤ bill (-4) (clim A (f k)) from hq.mono fun _ h hp i j L S hi => h i j L S hi hp
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun L => eventually_all.mpr fun S => ?_
  have htv : 0 < b := by linarith
  obtain ⟨C,cP,he⟩ := fence (n:=n) L S
  let a₁ := 1/(2:ℝ)
  filter_upwards [eventually_all.mpr (fun (i:Fin n×KeyIn G d) => eventually_all.mpr fun j=>covers H ha f hf x t ht hc hu a₁ (by unfold a₁;norm_num) i j),((hat_rate A H).comp hf).eventually (transports (b:=b + -4) (show a₁<b + -4 by dsimp [a₁]; linarith) (C*a₁))]
    with k hv hh hi hR
  let s:= clim A (f k); intro T r
  have hr : 1 ≤ r := by dsimp only [r]; rw [mag_bill]; exact Glimmer.costed _ _ htv.le
  apply le_of_mul_le_mul_left _ (zero_lt_one.trans_le hr)
  refine (he T (Ship.fitting hR) i j hi (a₁*bill a₁ s) (by unfold a₁ bill; positivity) (fun p q => ?_) _ hr).trans ?_
  · exact (Complex.abs_re_le_norm _).trans (hv (i,p) (j,q) hR)
  change C*(a₁*_ ) ≤ r*_;rw [show r=_ from mag_bill A b (f k),overlap,← mul_assoc]; exact hh

open YM.Next.Rank.Read
omit hc in
lemma coughR (B : Fin n→ (standard C).Tag)(hc':∀ i,tested C.path.levels b (f i) (x i)= t i • a) :
    ∀ᶠ k in atTop, sufficiently C B b (x k) (f k):= by
  let Y := C.path.levels; let h := fun x : Points n => Read.maxProfile C x B
  let D := fun x => Exponential.roll (h x) (Fintype.card (Fin n))
  obtain ⟨z,hz⟩:= profile_wind a ha t ht hu B; let u:=Exponential.roll z (Fintype.card (Fin n))
  have hp : Tendsto (fun k => D (Station.tested Y b (f k) (x k))) atTop (𝓝 u) := by
    unfold D; simp_rw [show ∀ k,Station.tested Y b (f k) (x k)=t k • a from hc']
    exact (Exponential.roll_cont _).continuousAt.tendsto.comp hz
  have he i : ∀ᶠ k : ℕ in atTop, ‖(D (Station.tested Y b (f k) (x k))).part i‖ ≤ bill (1/4) (Y.clock.hatBeta (f k)) := by
    have hx := ((tendsto_pi_nhds.1 hp i).norm).eventually (ge_mem_nhds (lt_add_one (‖u.part i‖)))
    filter_upwards [hx, ((bill_lo (a:=1/4) (by norm_num)).comp ((hat_rate Y H).comp hf)).eventually_ge_atTop (‖u.part i‖+1)] with k hp hq
    exact le_trans hp hq
  filter_upwards [eventually_all.mpr he] with k hv hh p N hi j
  let T := Ship.yard C b hi p
  have hf := Read.cumulative C (tested Y b (f k) (x k)) B (Ship.fitting hh)
  have hp : Ship.targets C B hh=D (tested Y b (f k) (x k)) := Exponential.Expands.uniq hf (Exponential.rolls _ (Read.profile_vac _ (Maxwell.table_regular C.labels) _ (Ship.fitting hh) B))
  rw [hp,view]; unfold Array.reorient; split_ifs <;> simpa only [shade_part, Poly.part_neg,norm_star,norm_neg] using! hv j.2.val
end YM.RG12.Rail
