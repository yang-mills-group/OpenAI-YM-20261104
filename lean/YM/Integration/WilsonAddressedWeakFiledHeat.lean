import YM.Integration.WilsonAddressedWeakDisplacedWick
import YM.Integration.WilsonAddressedWeakFiledSalary

/-! Pay the actual finite self-contraction before applying the displaced Maxwell test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFiledHeat
open Function Filter RG Lattice Wilson Marker Cells Next.Rank
open Ribbon Spindle Configuration Normal Rise Perch Glimmer LiftMark Beamer Station Atlas Tariffs Tapes MvPolynomial
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {k p b d H D:ℕ}

theorem contracted {X:Type*} (Q:Normal.Symmetric X) (P:poly X) (h:P.totalDegree≤D)
    (t:ℝ) (pos:1≤t) (hc:∀ i j,‖Q.cov i j‖≤t) :
    coin (milk Q P) ≤ coin P*((2*(D+2:ℝ))^D*t^D) ∧ (milk Q P).totalDegree≤D := by
  let K:Valve X X:=⟨fun i=>Finsupp.single i 1,Q⟩
  have paid:K.Fair t:=by
    refine ⟨pos,?_,hc⟩
    intro i
    change coin (glyph (Finsupp.single i (1:ℂ)))≤t
    simpa [glyph,coin] using pos
  have eq:K.read P=milk Q P:=by
    rw [Valve.read,pipes]
    change (Normal.exchange (fun i:X=>Finsupp.single (id i) 1)) _=_
    rw [←Normal.labelled,MvPolynomial.rename_id];rfl
  have full:=Tapes.crux paid P D h
  rw [eq] at full
  refine ⟨full.1.trans_eq ?_,full.2⟩
  change _ * ((2*(D+2:ℝ))*t)^D=_
  rw [mul_pow]

theorem paid (simple:G.Simple) (v:C.label d) (arc:ℝ) (D:ℕ) :
    ∀ᶠ k:ℕ in atTop,∀ {b p:ℕ} (wide:4*b≤wood C.path.levels k)
      (Y:AtlasData G C.S p) (_:Hail C k p D Y) (W:poly (slotC G b)),
      let s:=clim C.path.levels k
      let F:=C.labels.level d
      (W.totalDegree≤D) →
      (coin W≤(2*bill (5/8) s)*((2*2^leash F*F.coeffSize v)*bill (arc*d+(leash F:ℝ)) s)) →
      coin (WilsonAddressedWeakDisplacedWick.heat wide Y W)≤bill (arc*d+Atlas.saves C d) s ∧
        (WilsonAddressedWeakDisplacedWick.heat wide Y W).totalDegree≤D := by
  let A:=C.path.levels
  let F:=C.labels.level d
  let γ:=arc*d+(leash F:ℝ)
  let fee:ℝ:=2*(2*2^leash F*F.coeffSize v)*(2*(D+2:ℝ))^D
  have saved:γ+(5/8:ℝ)+1/4 < arc*d+Atlas.saves C d:=by
    change arc*d+(leash F:ℝ)+_+_ < arc*d+((leash F:ℝ)+2);linarith
  filter_upwards [(hat_rate A simple).eventually (transports saved fee)] with k room b p wide Y hail W s F' deg rate
  let Q:=control (k:=k) Y 0 (wood A k)
  let P:=rename (calls wide) W
  have coins:coin P≤coin W:=by
    unfold P; rw [Normal.labelled]
    have h:=rise (fun z:slotC G b=>Finsupp.single (calls wide z) (1:ℂ)) 0 zero_le_one
      (c:=1) le_rfl (fun z=>by simp) W le_rfl
    simpa only [one_pow,mul_one] using h
  have full:=contracted Q P ((totalDegree_rename_le ..).trans deg) (tin s D) (tincost s D) hail.2
  refine ⟨full.1.trans ?_,full.2⟩
  have grade:shade D*(D:ℝ)≤1/4:=by
    have positive : 0 ≤ LiftMark.shade D := by unfold LiftMark.shade; positivity
    linarith only [shade_thin D,positive]
  have small:(tin s D)^D≤bill (1/4) s:=by
    unfold tin; rw [Glimmer.bills];exact Glimmer.billed s (by simpa [mul_comm] using grade)
  calc
    coin P*((2*(D+2:ℝ))^D*(tin s D)^D)
        ≤ ((2*bill (5/8) s)*((2*2^leash F*F.coeffSize v)*bill γ s))*((2*(D+2:ℝ))^D*bill (1/4) s) :=
          mul_le_mul (coins.trans rate) (mul_le_mul_of_nonneg_left small (by positivity)) (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (tincost s D)) _))
            (le_trans (Rise.sign _ _ zero_le_one) rate)
    _ = fee*bill (γ+(5/8:ℝ)+1/4) s := by
      have eq:bill (γ+5/8+1/4) s=bill γ s*bill (5/8) s*bill (1/4) s:=by rw [overlap,overlap]
      rw [eq];unfold fee;ring
    _ ≤ _ := room

end YM.Integration.WilsonAddressedWeakFiledHeat
