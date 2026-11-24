import YM.GradedFar.Jiffy
import YM.GradedFar.StampDuty
/-!
# Through polynomial expansions of the partially spent frame-group

Start= leading, log clocks and all field caps exact. Need not assume positive of the
intermediate **formal** clocks. Errors admissible every requested order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ) (h p:ℕ)
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "F'" => firm Z M ν h
local notation "χ" => ofPS
local notation "B'" => fare Z M ν h p
local notation "J'" => ticker Z M ν p

lemma liable : Hands (pairField G h):=⟨1,zero_le_one,fun _ _=>by rw [one_mul]; exact norm_mul_le ..⟩
include H
lemma owed {Iota:Type*} {L x:Iota→ℝ}{z:Iota→ℂ}(hv:Charge L (fun i=> (x i:ℂ)))(hz:Charge L z):
    Beyond (p+1) z L (fun i=> B' (L i) (z i) * B' (x i) (J' (L i) (z i)) - B' (L i+x i) (z i)) ∧
    Beyond (p+1) z L (fun i=> J' (x i) (J' (L i) (z i)) - J' (L i+x i) (z i)):= by
 have hx:= Charge.id (L:=L); have hc:= days_cost Z M ν H hx; have hr:= field_cost Z M ν H h hx; have hp:= field_cost Z M ν H h hv
 have hD:= omitted_interpose p (c:=fun i=>ϕ (L i)) hp hc (fun i=> ((H.dilation ν).check.led (L i)).start) hz
 have hB:= omitted_pair (L:=L) (liable h) p hr (together_sub hp (c:=fun i=>ϕ (L i)) hc) hz
 have hR:= (Beyond.pair_right (liable h) (total_crop p hz hr) hD).add hB
 unfold fare ticker; constructor
 · simp_rw [hands Z M ν H]; refine Eq.mp ?_ hR; congr! 1; funext i; rw [map_sub]; simp only [pairField_value]; abel
 simp_rw [days Z M ν H]; exact omitted_interpose p (row_cost Z M ν H hv) hc (fun i=> ((H.dilation ν).check.led (L i)).start) hz
lemma tick_tangent (x:ℝ) (z:ℂ): ∑ i∈ Finset.range 2, z^i • χ (ϕ x) i=z:= by
 let hv := (H.dilation ν).check.led x
 have hp:χ (ϕ x) 1=1:=hv.lead; have ht:χ (ϕ x) 0=0:=hv.start
 rw [Finset.sum_range_succ,Finset.sum_range_one,pow_one,hp,ht]; simp
lemma field_tangent (x:ℝ) (z:ℂ): ∑ i ∈ Finset.range 2,z^i • F' x i=1:= by
 simp [Finset.sum_range_succ,firm,(H.dilation ν).check.paid x h|>.zero, stamp_one, start Z M ν H (η:=x) ]
 ext u i; simp

-- uniform on wide η both directions, last step bounded by request.
lemma budget_up (hv:1≤p)(D:ℝ):
    ∃ C:ℝ,1≤C ∧ ∃ k:ℕ, ∀ (t x:ℝ)(z:ℂ),|x| ≤ |D| → ‖z‖ ≤ 1 →
    let f:=C*(1+|t|)^k
    let y:=J' t z
    let u:=B' t z
    ‖u-1‖ ≤ f*‖z‖^2 ∧ ‖y-z‖ ≤ f*‖z‖^2 ∧
      ‖u*B' x y-B' (t+x) z‖ ≤ f*‖z‖^(p+1) ∧ ‖J' x y-J' (t+x) z‖ ≤ f*‖z‖^(p+1):=by
   let Ω:= ℝ × {u:ℝ//|u| ≤ |D|} × {z:ℂ//‖z‖ ≤ 1}; let L (i:Ω):=i.1; let x(i:Ω):=(i.2.1:ℝ); let z(i:Ω):=(i.2.2:ℂ)
   have H₀: Charge L z:= Charge.cap ⟨1,fun i=> i.2.2.property⟩
   have H₁: Charge L (fun i=> (x i:ℂ)):= Charge.cap ⟨|D|,fun i=> by rw [Complex.norm_real,Real.norm_eq_abs]; exact i.2.1.property⟩
   obtain ⟨hR,hT⟩:= owed Z M ν h p H H₁ H₀
   have he:= crop_suffix p 2 (by omega) (field_cost Z M ν H h (x:=L) Charge.id) H₀
   have hz:= crop_suffix p 2 (by omega) (row_cost Z M ν H (x:=L) Charge.id) H₀
   simp_rw [field_tangent Z M ν h H] at he; simp_rw [tick_tangent Z M ν H] at hz
   obtain ⟨k,h0,h1,h2,h3⟩:= (he.bound.and (hz.bound.and (hR.bound.and hT.bound))).exists
   obtain ⟨C,hC,h0,h1,h2,h3⟩:= ((eventually_ge_atTop 1).and (h0.and (h1.and (h2.and h3)))).exists
   exact ⟨C,hC,k,fun t x z hx hz=> let i:= ((t,⟨x,hx⟩,⟨z,hz⟩):Ω); show _ from ⟨h0 i,h1 i,h2 i,h3 i⟩⟩
lemma jiffy (D:ℝ): ∀ᶠ δ:ℝ in trail,∀ (t:ℝ)(z y:ℂ), |t| ≤ |D| → ‖z‖ ≤ δ→‖y‖≤δ→
    ‖B' t z-B' t y‖≤ ‖z-y‖ ∧ ‖J' t z-J' t y‖≤ 2*‖z-y‖:= by
 let Ω:={t:ℝ//|t| ≤ |D|}; let L(i:Ω):ℝ:=i.val; have hv: Charge (fun _=>0) (fun i=> (L i:ℂ)):= Charge.cap
   ⟨|D|,fun i=> by rw [Complex.norm_real,Real.norm_eq_abs]; exact i.property⟩
 have hB i: ‖F' (L i) 1‖ ≤ 0:= by rw [firm,start Z M ν H,map_zero,norm_zero]
 have hR i: ‖χ (ϕ (L i)) 1‖ ≤ 1:= by rw [ofPS, ((H.dilation ν).check.led (L i)).lead,norm_one]
 obtain hA:= universal (f:=fun i=> F' (L i)) le_rfl hB (field_cost Z M ν H h hv) p
 obtain hc:= universal (f:=fun i=> χ (ϕ (L i))) zero_le_one hR (row_cost Z M ν H hv) p
 filter_upwards [hA,hc] with δ hA hc t z y ht hz hy
 specialize hA ⟨t,ht⟩ z y hz hy; specialize hc ⟨t,ht⟩ z y hz hy; rw [add_zero,one_mul] at hA
 rw [one_add_one_eq_two] at hc; exact ⟨hA,hc⟩
end YM.Integration.GradedFar.Neighbor
