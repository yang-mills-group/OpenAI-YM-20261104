import YM.Integration.WilsonThermometerWardBareScene

/-! Keep each native marked source's own raw wage at its actual root.
The physical word roster, original seed paths and angular coefficients are fixed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerIndividualSourceWallet
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonOriginalStarSceneRent
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) {V:Type} [DecidableEq V] [Fintype V]
  (d:V→ℕ) (v:(j:V)→R.family.label (d j))

def charge (j:V):ℝ:=(R.family.labels.level (d j)).coeffSize (v j)

def aperture (σ Ω:ℝ) (j:V):ℝ:=(1+charge R d v j)*max 1 (wallet R d σ)*Ω

omit [DecidableEq V] [Fintype V] in
theorem rent_nonnegative (j:V):0≤charge R d v j:=Work.G08.size_nonneg ..

omit [DecidableEq V] in
theorem funded (σ Ω:ℝ) (one:1≤Ω) (j:V):1≤aperture R d v σ Ω j:=by
  apply one_le_mul_of_one_le_of_one_le _ one
  exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (rent_nonnegative R d v j)) (le_max_left ..)

omit [DecidableEq V] [Fintype V] in
/-- A single real slot is enrolled on the original raw dictionary at this root. -/
theorem socket {g τ:ℝ} (ready:0≤g) (warm:0<τ) (band:g≤2*τ) (i:Entry R d):
    ‖scalar R d g τ v i‖≤charge R d v (root R d i)*stencil R d i:=by
  rcases i with j|⟨j,p⟩
  · exact controlled R (fun _:Unit=>d j) g τ (fun _=>v j) (K:=charge R d v j)
      (fun _=>le_rfl) ready warm band (.inl ())
  · exact controlled R (fun _:Unit=>d j) g τ (fun _=>v j) (K:=charge R d v j)
      (fun _=>le_rfl) ready warm band (.inr ⟨(),p⟩)

omit [DecidableEq V] in
theorem billable (σ Ω g τ:ℝ) (one:1≤Ω) (ready:0≤g) (warm:0<τ) (band:g≤2*τ):
    bill R d σ g τ v (fun j=>(aperture R d v σ Ω j)⁻¹)≤Ω⁻¹:=by
  let T:=max 1 (wallet R d σ)
  have tp:0<T:=zero_lt_one.trans_le (le_max_left ..)
  have op:0<Ω:=zero_lt_one.trans_le one
  calc
    _ ≤(T*Ω)⁻¹*wallet R d σ:=by
      rw [bill,wallet,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      let K:=charge R d v (root R d i)
      let W:=normalizer (raw R d i) σ*stencil R d i
      have kp:0≤K:=rent_nonnegative R d v _
      have core:0 ≤ stencil R d i:=by cases i <;> simp [stencil]
      have wp:0≤W:=mul_nonneg (positive (raw R d i) σ).le core
      have paid:=mul_le_mul_of_nonneg_left (socket R d v ready warm band i)
        (positive (raw R d i) σ).le
      have controlled:wage R d σ g τ v i≤(1+K)*(1+W):=by
        unfold wage
        dsimp only [K,W]
        nlinarith only [paid,kp,wp]
      let X:=Real.exp (σ*(raw R d i).length)
      have xp:0≤X:=(Real.exp_pos _).le
      have ap:0≤(aperture R d v σ Ω (root R d i))⁻¹:=inv_nonneg.mpr
        (zero_le_one.trans (funded R d v σ Ω one _))
      calc
        _ ≤(aperture R d v σ Ω (root R d i))⁻¹*(((1+K)*(1+W))*X):=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right controlled xp) ap
        _ =(T*Ω)⁻¹*((1+W)*X):=by
          change ((1+K)*T*Ω)⁻¹*(((1+K)*(1+W))*X)=_
          have non:(1+K)≠0:=(by linarith only [kp] : 0<1+K).ne'
          field_simp
    _ ≤(T*Ω)⁻¹*T:=mul_le_mul_of_nonneg_left (le_max_right ..) (inv_nonneg.mpr (mul_pos tp op).le)
    _ =_:=by field_simp

end YM.Integration.WilsonThermometerIndividualSourceWallet
