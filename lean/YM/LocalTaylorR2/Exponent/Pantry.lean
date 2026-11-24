import YM.LocalTaylorR2.Exponent.Rack
import YM.LocalTaylorR2.Reel.Strand

/-!
 # Buy the manner of Pry. μL J chosen before N. Keep old Crib & co-extrapolated phases & perception. No fast fluct.O.Cost in typical region. Do not assert an Expansion for high graph-order off-axis here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Reel Strand Tender PhysicalNext.Repeat Mesh
variable {e r B w b ζ ρ :ℝ} {U: Utopia H j v d r w χ} {Φ Δ:Bevy T}
-- Augment Meter hashes keeping startup trajectory. No borrow proof needed. Then lodge BOTH models.
lemma negotiations (U:Utopia H j v d r w χ)(hU:LocalBookingsR2 ζ e U) (ht:1≤betaF G s L)(hζ:0≤ζ)
    {p':LogIndex c f→ℝ}(h: Mesh.Meter (H:=H) Φ p ζ r v d ρ B j χ p')(hh: Hallmarked H Φ Δ j k ζ b D v d χ) (hq:e+(B+b)≤ Q.goal L s)(hp:0<ρ)(hD:0≤D):
   ∃ V:Utopia H j v d r w χ, LocalBookingsR2 ζ (e+(B+b)) V ∧ Crib Φ V p ρ ∧
     (∀ i,Port.Burst H (H.supportP (identityLog i)) (Δ i)) ∧ ∀ t:Strand, Lodestar H k (1+ρ^p*D) V (replay (weightLog H) Δ (Strand.dial t*ρ^p)):=by
  obtain ⟨f',hf,hA⟩:= hh.vivre
  have hx {g:LogIndex c f→ ℝ} {b} (h: Sales (radiusB s) Q.relative Q.ε (roadway T R (radiusB s) Q.halo) (fun i=>betaF G s L^leaseLog ζ c f i*g i) (exCharge T R) b) :∀ i,0≤g i:=fun i=> nonneg_of_mul_nonneg_right (h.nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le ht) _)
  have hp':= hx h.hashes; have hf':= hx hf
  let z' :=p'+f'; let d₁:=1+ρ^p*D; have h₁:1≤d₁:= le_add_of_nonneg_right (mul_nonneg (pow_nonneg hp.le _) hD)
  have hT: Mesh.Meter (H:=H) Φ p ζ r v d ρ (B+b) j χ z':= by
     refine ⟨h.keptP,?_,fun i=>(h.tick i).climb H (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hf' i)) (by positivity)) le_rfl⟩; convert! Mesh.nab h.hashes hf using 1; ext i; unfold z'; rw [Pi.add_apply,mul_add]; rfl
  obtain ⟨V,hV,hR⟩:= Mesh.increasing U hU Φ ht hζ hT hq
  have hΔ i: Port.Burst H (H.supportP (identityLog i)) (Δ i):= by
    rw [show Δ i=Δ i-Φ i+Φ i from (sub_add_cancel ..).symm]; exact Port.Burst.plus (hA i).upheld (Port.Burst.fat (h.keptP _))
  refine ⟨V,hR,⟨h.keptP,fun j=>(hT.tick j).climb H (by rw [hV,inv_pow]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Tender.logN ..)) (inv_nonneg.mpr (pow_nonneg hp.le _))) le_rfl⟩, hΔ,?_⟩
  intro t; refine ⟨fun i=> (population (Port.Burst.fat (logTest H i)) (hΔ i) Strand.dial (ρ^p)).land t,?_⟩
  intro i Y hy E _ _ _ F X U' u z x Z hX hW hΨ hχ hm hF
  have hs:= h.tick i E F X U' u z x Z hX hW hΨ hχ hm hF; obtain ⟨hk,hΛ⟩:= (hA i).power E F X U' u z x Z hX hW hΨ hχ hm hF _ hy; let V' i:= vary X (U' i); let R':= glacial X Y Z R.beta (o.ξ/2) d₁ k
  have hr:= Charge.logSees hU i E F X U' u z x Z hX hW hΨ hχ hm hF; let H' x:=(Δ i-Φ i) F (V' x) (z x); let K x:= weightLog H i F (V' x) (z x); let h' x:= (Φ i- weightLog H i) F (V' x) (z x)
  let v' := Strand.dial t *ρ^p; have ht: ‖v'‖≤ρ^p:=by unfold v'; rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hp.le _)]; exact mul_le_of_le_one_left (pow_nonneg hp.le _) (abs_le.mpr t.property)
  rw [hV]; have hR' := frozenWide (β:=R.beta) (x:=o.ξ/2) (k:=k) X Y Z h₁
  have hx : Brush j (p' i*R'^1) (r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i)) (fun x=> v'*h' x) x:=by
     apply ((hs.smul v').opposite.shimmy ?_).climb _ le_rfl
     · exact Eventually.of_forall fun y=> (by change v'*(Φ i F (V' y) (z y)-K y)= -(v'*(K y-Φ i F (V' y) (z y))); ring)
     rw [pow_one]; apply le_trans (mul_le_mul_of_nonneg_right ht (by exact hs.nonneg : 0 ≤ p' i*(ρ^p)⁻¹)); apply le_trans _ (le_mul_of_one_le_right (hp' _) hR'); exact le_of_eq (by field_simp)
  have hz:Brush j (f' i* R'^1) (r*spanW T R (radiusB s) Q.halo (identityLog (S:=S) i)) (fun x=> v'*H' x) x:=by
    have hl:0 ≤ f' i*R'^1:= by rw [pow_one]; exact mul_nonneg (hf' _) (zero_le_one.trans hR')
    by_cases ht':Z∈eerie X Y (o.ξ/2) R.beta; swap; · refine Brush.zi ((hΛ ht').mono (fun x hx=> ?_)) hl hr.pos; change v'*H' x=0; rw [show H' x=0 from hx,mul_zero]
    have he:1≤ r:=U.active
    refine (hk.smul v').climb ((mul_le_mul_of_nonneg_right ht hk.nonneg).trans ?_) (le_mul_of_one_le_left hk.pos he)
    rw [pow_one]; unfold R' glacial; rw [if_pos ht', ←show X.B=radiusB s from congr_arg _ hX]; let V := facescale (edgesM S Y X.B) Z; have hx:1≤V:= (Flux.expenses ..).1
    apply le_trans (b:= f' i*(ρ^p*D*V^k)) (le_of_eq (by unfold V; ring)); apply mul_le_mul_of_nonneg_left _ (hf' _); exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx) _)
  have he : 1 ≤ R'^1:=one_le_pow₀ hR'
  have hc:= (hr.climb (le_mul_of_one_le_right (Tender.logN U i) he) le_rfl).gathering (hx.gathering hz)
  apply hc.shimmy (Eventually.of_forall ?_)|>.climb (le_of_eq ?_) le_rfl
  · intro x'; change K x'+v'*(Δ i F _ (z x')- K x') = K x'+(_ + _); unfold H' h' K; dsimp only [Pi.sub_apply]; ring -- implicit goals order
  dsimp only [Pi.add_apply,z',R',d₁]; ring
end YM.LocalTaylorR2.Exponent
