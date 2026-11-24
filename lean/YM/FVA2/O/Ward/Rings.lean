import YM.FVA2.O.Ward.Tail
/-!
# Pieces for actual continuum lines
Static budgets all rows at *one fixed scale*; no formal commutations over divergent integrals.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect
local notation "Π0"=> Job.single Unit
variable {G:Gauge}{s:ℝ}{U V:Edge G}{f g:Law G}{a b:QP→ℂ}
lemma depot {E D:Type}[NormedAddCommGroup E][NormedAddCommGroup D]{f:E→ℂ}{g:D→ℂ}
   (h:Shrink f)(hv:Shrink g): Shrink fun x:E×D=> f x.1*g x.2 := by
    refine ⟨ (h.smooth0.comp continuous_fst).mul (hv.smooth0.comp continuous_snd), fun k=>?_⟩; obtain ⟨C,hC,hW⟩:= h.env k; obtain ⟨D,hD,hL⟩:= hv.env k; refine ⟨C*D,mul_pos hC hD,fun i=>?_⟩; rw [norm_mul]; refine (mul_le_mul (hW _) (hL _) (norm_nonneg _) ( by positivity )).trans ?_; simp only [Prod.norm_def]; rw [div_mul_div_comm]; gcongr _ / ?_; rcases le_total ‖i.2‖ ‖i.1‖ with ht|ht
    · rw [max_eq_left ht]; exact le_mul_of_one_le_right (pow_nonneg (by positivity) _) (one_le_pow₀ (by simp))
    rw [max_eq_right ht]; exact le_mul_of_one_le_left (pow_nonneg (by positivity) _) (one_le_pow₀ (by simp))
lemma doubly (h:Rolled U)(hm:Rolled V)(hp:f∈ Wallet G)(l:Legs (Mode (BH G) QP)): Integrable (fun x:QP×QP=> trc U x.1 (trc V x.2 f) l) (planeF.prod planeF):= by
    let E := (QP × QP) × ℝ; let X:= ContinuousLinearMap.fst ℝ QP QP ∘L ContinuousLinearMap.fst ℝ (QP × QP) ℝ; let Y:= ContinuousLinearMap.snd ℝ QP QP ∘L ContinuousLinearMap.fst ℝ (QP × QP) ℝ; let L:= Wire.lift (Wire.ray l) (ContinuousLinearMap.snd ℝ (QP× QP) ℝ)
    simp_rw [at_trc, Finset.mul_sum, ← mul_assoc]; refine integrable_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=>integrable_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>?_))))
    have hL := Envelope.at_one (permits.mp hp E ((a,Y)::(b,-Y)::(i,X)::(j,-X)::L)); refine ( (depot ( Shrink.line (lineOf h i j)) (Shrink.line (lineOf hm a b)) ).mul (?_)).ready _; simpa [fieldVal, X,Y,L, Wire.lift_sail,show ∀ p:QP×QP,(ContinuousLinearMap.fst ℝ (QP×QP) ℝ) (p,1)=p from fun _=>rfl,show ∀ p:QP×QP,(ContinuousLinearMap.snd ℝ (QP×QP) ℝ) (p,1)=(1:ℝ) from fun _=>rfl] using hL
lemma wise (h:f∈ Wallet G)(hu:Rolled U)(he:Symm (field Landau.parity) f): Wise planeF f U (Q G 0) := ⟨ hu.pays Geo.Coherent h, hu.pays Geo.Coherent (hu.orb Geo.Coherent h), hu.pays Geo.Coherent (Rolled.up h), doubly hu hu h, he⟩
lemma budget (h:f∈ Wallet G)(he:Symm (field Landau.parity) f): Pieces0 (A0 G s 0) (B0 G s 0) (Q G 0) planeF f := ⟨ rA.pays Geo.Coherent h, rB.pays Geo.Coherent h, rA.pays Geo.Coherent (rB.orb Geo.Coherent h), rB.pays Geo.Coherent (rA.orb Geo.Coherent h), rA.pays Geo.Coherent (Rolled.up h), rL.pays Geo.Coherent h, doubly rB rA h, he⟩
variable {F H:ℕ→Law G}
lemma pieces (hf:∀ k,F k∈Wallet G)(hH:∀ k,H k∈Wallet G)(h1:∀ k,Symm (field Landau.parity) (F k))(h2:∀ k,Symm (field Landau.parity) (H k))(hx:∀ k,Pure (field Landau.parity) false (F k)): Pieces (A0 G s 0) (B0 G s 0) (Q G 0) planeF F H:= ⟨ fun k=> budget (hf k) (h1 k),fun k=> budget (hH k) (h2 k),hx,fun k j=> rB.pays Geo.Coherent (rA.on_tree (hf k) (hH j)), fun k j=> rA.pays Geo.Coherent (rB.on_tree (hf k) (hH j)), fun k j=>colors (hf k) (hH j) rA rB (reverse_b G s 0), fun k j=>colors (hf k) (hH j) rB rA (reverse_a G s 0), cl_a G s 0, cl_b G s 0, (cue G s 0|>.symm) ▸ cl_c G s 0, reverse_a G s 0, reverse_b G s 0 ⟩
end YM.FVA2.O.Ward
