import YangMills.WilsonProof.NativeSupport.Commissioned259.Convert

/-!
# Cancellation against the graded Far legs

`s = log T`. Even with through-h centre subtractions, and for every term surviving the basis
expansions (including at grade zero), **use the entire family of signed coefficients**, not
termwise estimates through a different frame. See also the dedicated price on this same
`looseT` in `O/Read/Zone : price_yard`; here retain also the homogeneous full and center
prices, then extend all three to the actual unit balls/mixed caps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Rake MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {V : Arenas G} {R : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    {n m H h : ℕ} (L : Law V R B) (P : O.Canon.Physical V R B)
    {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H) (he : ∀ i, e i ≤ H) (hh : h ≤ H)
    {K : Set (Points n)} {S : Set (Points m)} (hK : IsCompact K) (hc : K ⊆ conf n)
    (hS : IsCompact S) (hy : S ⊆ Outside m)
    (u : Scan G n) (v : Scan G m)
local notation "Ω" => install V
local notation "Cₓ" => FarCoefficients V

section
include L
/-- Termwise price cancellation: enough for full (a=0), center (a=w(q)), signed full-minus-
center residual (a=h+1). `ChargeP` exponents ADD under genuine power series multiplication. -/
lemma term_charge {I : Type} {a : ℝ} {f : I → ℝ → PowerSeries ℂ} (p : ℕ)
    (hf : ChargeP p (a+(totalG v:ℝ)) f) (j : LivesP v) : ChargeP p a (fun i s =>
      (∏ i, columnEntry B (-s) (v i) (j i)) * f i s) := by
  simp_rw [product_account, mul_assoc]
  have hp : ChargeP p 0 (fun (_ : I) s => play (seats (B (-s))) v (decode v j)) :=
    ChargeP.extreme (O.Enh.Uniform.flips (rhythm_v L)) _ _
  refine (ChargeP.joint (f:=fun (_ : I) s => Acres (-s) (totalG v)) reflectV
    (ChargeP.times hp hf)).grow ?_
  linarith

include P hS hy hK hc
lemma basis_full_charge (hu : budgeted u d) (hv : budgeted v e) (p h : ℕ) :
    ChargeP p 0 (fun (i : ↥K × ↥S) s =>
      measurement V B hd he i.1.val (squeeze (-s) i.2.val) (-s) (inputs u hu) (inputs v hv)) := by
  simp_rw [measured_basis L P.dimensions]
  refine ChargeP.sum _ fun j _ => term_charge L v p ?_ j
  exact (zero_add (totalG v:ℝ)).symm ▸ Ffull P u (decode v j) hK hc hS hy p h

variable (q : Toon G h)
omit hK hc in
lemma basis_center_charge (hv : budgeted v e) (p : ℕ) :
    ChargeP p (heft (flash q) : ℝ) (fun (i : ↥S) s =>
      center V B he (squeeze (-s) i.val) hh (-s) (theory q) (inputs v hv)) := by
  have hs : budgeted (Single (flash q)) (fun _ => h) := fun _ => size_le q
  unfold center
  simp_rw [show (fun (_ : Fin 1) => theory q) = inputs (d:=fun _=>h) _ hs from rfl, measured_basis L P.dimensions]
  exact ChargeP.sum _ fun j _ => term_charge L v p
    (F1 P (decode v j) hS hy (flash q) p) j

lemma basis_gap_charge (hu : budgeted u d) (hv : budgeted v e) (p : ℕ) :
    ChargeP p ((h:ℝ)+1) (fun (i : ↥K × ↥S) s =>
      measurement V B hd he i.1.val (squeeze (-s) i.2.val) (-s) (inputs u hu) (inputs v hv) -
        ∑ q : Toon G h, Cₓ u i.1.val (flash q) *
          center V B he (squeeze (-s) i.2.val) hh (-s) (theory q) (inputs v hv)) := by
  -- The power-series subtraction `O.Read.looseT` is on these literal operands
  simp_rw [identifies_show L P.dimensions, identifies_long L P.dimensions]
  change ChargeP p ((h:ℝ)+1) (fun (i : ↥K × ↥S) s =>
    O.Read.looseT B Ω s u v (Cₓ u) h i.1.val i.2.val)
  simp_rw [O.Read.loose, O.Read.LensT, concert, Finset.mul_sum]
  -- retain the T^{-(h+1)} factor per basis/every signed gap
  refine ChargeP.sum _ fun j _ => ?_
  have H := term_charge L v p (a:=(h:ℝ)+1) (FO P u (decode v j) hK hc hS hy p h) j
  simp_rw [product_account, mul_assoc] at H
  exact H
end
end YM.FVA2.GradedFar259
