import YM.RG01Estimate.ValueRead
/-!
# The paid scalar part. Extensive cost kept explicitly, no summation in
 coupling. For every auxiliary period; translational consumers must keep
 their own scalar and per-site extraction. This also prices φ with β
 multiplying it. The small price of this remainder does not by itself
 imply cancellation of each displayed negative power (compare in exact
 model including the lower prescriptions and clusters).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace.Stellar
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree Matrix
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {c f L:Side}{S:StepData c f}(F:Forest S.ratio)(T:Tube G S)(k:S.Choices)
   (ρ:Bid.Dir G c→AxisChart G F)(O:ChartRatio G)
local notation "X" => Positions (Uniform.Primary c G)
local notation "Y₀" => Poll.Body (Precision.Key F G)
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "Θ" => Lapis.table F k T.up T.high
local notation "ψ" => mist F O T.up
local notation "q" => Lapis.orbit F ρ

def path (x:ℝ× X):= (rho x).2
-- ctx notation X references only c G; no F

def pressure (x:ℝ× X):= Θ ((rho x).2,q (rho x).2)
def entropy (x:ℝ×X):= ψ ((rho x).2,q (rho x).2)+(Lantern.shade M (rho x).2-Lantern.shade M 0)

def model (j:ℕ)(β:ℝ)(y:X) := Real.log (solar F O β)-Lantern.shade M 0 -
      (β*trunc (Stellar.pressure F T k ρ) (j+2) (gStep β) y + trunc (entropy F T k ρ O) j (gStep β) y)
def logprice (β:ℝ)(y:X) := Real.log (price F T O k ρ β (gStep β • y))
variable {j n:ℕ} {u v b τ D R σ:ℝ}
def joints (_k : ℕ)(C:ℝ) := let h:= 1+C; h+h
def axial (k:ℕ)(C Y:ℝ):= clump k (expense k Y) (clump k (joints k C) C)
def luxury (k:ℕ)(C Y:ℝ):= axial k C Y + clump k (expense k Y) C

lemma panel {v:ℝ} {f:X→ℝ} (x:ℝ×X) (hp : ‖x.1‖≤1) (hY: 1≤ R) (hs:‖x.2‖≤ R) (h: Brush j v 1 f (rho x).2) : Brush j (clump j (expense j R) v) 1 (fun x=> f (rho x).2) x:= by
   let B:= ContinuousLinearMap.snd ℝ ℝ X
   have he:= Brush.reading B (show Brush j v 1 f (B (rho x)) from h) (ContinuousLinearMap.norm_snd_le ..); rw [one_mul] at he
   have h:= composite (travel_cap x hp hY hs) he; exact h

variable (H : Golf (Lapis.table F k T.up T.high) (mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) j D u u τ)
local notation "e" => (ball (0:X) R)
local notation "Y" => corridor b e
include H
lemma pillar (hP:b*R≤u) (hY:1 ≤ R) (hh:b≤u) (x:ℝ × X)(hx:x∈Y) : Brush (j+2) (axial (j+2) τ R) 1
         (Stellar.pressure F T k ρ) x ∧ Brush j (luxury j τ R) 1 (entropy F T k ρ O) x:= by
  have hB : ‖x.1‖≤ 1:= (mem_ball_zero_iff.mp hx.1).le.trans (hh.trans H.small)
  let f y:=(y,q y); let z:= (rho x).2
  have hf:= mem_ball_zero_iff.mp hx.2; have h₁ : ‖z‖<u:= (norm_snd_le (rho x)).trans_lt (lt_of_lt_of_le ((rho_mem x hY hf).trans_lt (mul_lt_mul_of_pos_right (mem_ball_zero_iff.mp hx.1) (zero_lt_one.trans_le hY))) hP)
  have hp:= H.curve _ h₁
  have hg: Brush (j+2) (joints (j+2) τ) 1 f z:= by
     let L:=ContinuousLinearMap.id ℝ X
     have he : Brush (j+2) 1 1 L z:=Brush.linearB _ (h₁.le.trans H.small) ((ContinuousLinearMap.norm_id_le).trans_eq (mul_one _).symm) zero_le_one
     exact (he.climb (le_add_of_nonneg_right hp.nonneg) le_rfl).pair (hp.climb (le_add_of_nonneg_left zero_le_one) le_rfl)
  have hU : ‖(0:ℝ)‖ < u:= by rw [norm_zero]; exact H.pos
  obtain ⟨hv,hD⟩:= H.color 0 0 (0,z) (show ‖(0:Y₀)‖ ≤ D by rw [norm_zero]; exact H.off) (by simp) hU h₁
  rw [show Lantern.visit q 0 0 (0,z)= (z,q z) from by simp [Lantern.visit] ] at hv hD
  exact ⟨panel x hB hY hf.le (composite hg hv),(panel x hB hY hf.le (composite (hg.smaller (show j≤j+2 by omega)) hD)).gathering (panel x hB hY hf.le (H.gram _ h₁).2)⟩

lemma back (hO: LocalRatio O) (hP:b*R≤u) (hY:1 ≤ R) (hh:b≤u) (β:ℝ)(he : 0<β)
    (y:X)(hy:(gStep β,y)∈ Y) {r:ℕ} (hl:n+r ≤ j): Brush n
     (gStep β^r * (axial (j+2) τ R + luxury j τ R)) 1 (fun y=> Stellar.logprice F T k ρ O β y - Stellar.model F T k ρ O r β y) y := by
  have hf x (h:x∈Y):= pillar _ _ _ _ _ H hP hY hh x h
  let d:=gStep β; have hk:= Fare.gS β he; have hd:0<d:=hk.1
  let Φ:= Stellar.pressure F T k ρ; let Ψ:= entropy F T k ρ O
  let C:= axial (j+2) τ R; let D':= luxury j τ R
  have hB:= (priced_defect Φ e b isOpen_ball d y hy (r+2) (fun x hx=> (hf _ hx).1.smaller (show n+(r+2)≤j+2 by omega))).smul β
  have hx:= priced_defect Ψ e b isOpen_ball d y hy r (fun x hx=> (hf _ hx).2.smaller hl)
  rw [Real.norm_of_nonneg he.le, abs_of_pos hd,pow_add] at hB; rw [abs_of_pos hd] at hx
  have hu:= sun F O β he hO
  have hN x: logprice F T k ρ O β x=Real.log (solar F O β)-Lantern.shade M 0- (β*Φ (d,x)+Ψ (d,x)):= by
      unfold logprice Courtyard.price; rw [Real.log_mul hu.ne' (Real.exp_pos _).ne',Real.log_exp]; unfold coverLog Φ Ψ Stellar.pressure entropy rho; dsimp only; unfold d; ring
  have hv:= (hB.gathering hx).smul (-1)
  refine (hv.climb (le_of_eq ?_) le_rfl).shimmy ?_
  · rw [norm_neg,norm_one,one_mul]; change β*(d^r*d^2*C)+_=d^r*(C+D'); rw [mul_add]; linear_combination (d^r*C)*hk.2
  filter_upwards with x
  change Stellar.logprice _ _ _ _ _ _ _ - _ = (-1:ℝ) • _
  rw [hN,Stellar.model]; simp only [Φ,Ψ,smul_eq_mul]; ring
end YM.RG01Estimate.Laplace.Stellar
