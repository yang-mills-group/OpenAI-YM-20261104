import YM.Integration.WilsonOriginalObservedRoseTruncatedFaces
import YM.Integration.WilsonMaxwellThermometerNominatedSecant

/-! Price an ordinary signed reading against the connected positioned Galop
polynomial. The seven comparisons with the issued ordinary figure keep their
own original, signed coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseFiniteReturn
open Finset PowerSeries RG Lattice Wilson PhysicalNext.Repeat.Legato
open Maxwell XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerConnected (value)
open WilsonMaxwellThermometerNominatedSecant (bill)
open WilsonOriginalObservedRoseTruncatedFaces (face fee)
open scoped Classical BigOperators
variable {G:Gauge} (W:Initialize G) {V:Store G} (x:Sample 3) (z:Tags G 6 3) (J:ℕ) (g:ℂ)
local notation "A" => WilsonOriginalObservedRoseProgram.face W (V:=V) x z
def row (s:Badge):ℂ:=(face (A) J s).eval g
def target:ℂ:=(PowerSeries.trunc (J+1) (WilsonOriginalObservedRoseProgram.entry W (V:=V) x z)).eval g
def edge (M:Badge→ℂ):ℂ:=
  let A':=row W (V:=V) x z J g
  ∑s:Badge,bill M A' s*(M s-A' s)
def charge (M:Badge→ℂ):ℝ:=
  let A':=row W (V:=V) x z J g
  ∑s:Badge,‖bill M A' s‖*‖M s-A' s‖
local notation "read" => row W (V:=V) x z J g
local notation "cooked" => target W (V:=V) x z J g
theorem cleared (M:Badge→ℂ)(observed older:ℂ)(γ:ℝ)(hg:‖g‖≤1)
    (bought:‖observed-value M-older‖≤γ):
    ‖observed-(cooked)-older-edge W (V:=V) x z J g M‖≤γ+fee (A) J*‖g‖^(J+1):=by
  have insert:=WilsonMaxwellThermometerNominatedSecant.signed M (read)
  change value M-value (read)=edge W (V:=V) x z J g M at insert
  have law:observed-(cooked)-older-edge W (V:=V) x z J g M=
      (observed-value M-older)+(value (read)-(cooked)):=by rw [←insert];ring
  rw [law]
  exact (norm_add_le ..).trans (add_le_add bought (WilsonOriginalObservedRoseTruncatedFaces.price (A) J g hg))

theorem total (M:Badge→ℂ)(observed older:ℂ)(γ:ℝ)(hg:‖g‖≤1)
    (bought:‖observed-value M-older‖≤γ):
    ‖observed-(cooked)-older‖≤γ+fee (A) J*‖g‖^(J+1)+charge W (V:=V) x z J g M:=by
  have h:=cleared W (V:=V) x z J g M observed older γ hg bought
  have inc:‖edge W (V:=V) x z J g M‖≤charge W (V:=V) x z J g M:=by
    unfold edge charge
    simpa only [norm_mul] using (norm_sum_le (Finset.univ:Finset Badge) (fun s=>bill M (read) s*(M s-(read) s)))
  calc
    _ = ‖(observed-(cooked)-older-edge W (V:=V) x z J g M)+edge W (V:=V) x z J g M‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le ..).trans (add_le_add h inc)

end YM.Integration.WilsonOriginalObservedRoseFiniteReturn
