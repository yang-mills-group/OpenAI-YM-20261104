import YM.Integration.WilsonOlderFreshGraphSlate
import YM.Integration.WilsonOriginalStarSceneRows

/-! One signed roster for the three compact word families at their original sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPointCompactRoster
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {I:Type} {q:ℕ} {σ:ℝ}
  (owner:I→Fin 3) (grades:Fin 3→ℕ) (sites:Fin 3→Site n)
  (T:(i:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner i)) q σ)
  (A:Fin 3→Set ℂ) (charge:I→ℂ)

abbrev Index := (i:I) × (T i).Roster
instance [Countable I] : Countable (Index owner grades T) := by
  haveI (i : I) : Countable (T i).Roster := inferInstance
  infer_instance

def home (v:Fin 3) := WilsonOriginalStarSceneRows.binder (fun _:Unit=>sites v) ()
def joint (v:Fin 3) := WilsonOriginalStarSceneRows.binder sites v
def alone (v:Fin 3) : Unit→Set ℂ := fun _=>A v
def subject (v:Fin 3) (t:Wallet A) : Wallet (alone A v) := fun _=>t v

local notation "J" => Stock.census (Fin 3)
local notation "campus" => Passport.point sites
local notation "single" z:max => (T (z).1).rows (home sites (owner (z).1)) (alone A (owner (z).1)) (z).2

def rows (z:Index owner grades T):Row campus J G (Wallet A) where
  binder := joint sites (owner z.1)
  lamp := (single z).lamp
  atom := (single z).atom
  lawful := (single z).lawful
  clear := (single z).clear
  salary := (1+‖charge z.1‖)*(single z).salary
  sound := mul_pos (by positivity) (single z).sound
  paint t := charge z.1 * (single z).paint (subject A (owner z.1) t)
  rank := (single z).rank

local notation "M" => rows owner grades sites T A charge

theorem support (z:Index owner grades T) : (M z).mode=(J).fire (owner z.1) := rfl

theorem nominal (z:Index owner grades T) (t:Wallet A) (g:ℝ) (U:Config G n) :
    (M z).nominal g t U = charge z.1 * (single z).nominal g (subject A (owner z.1) t) U := by
  change (charge z.1 * (single z).paint (subject A (owner z.1) t)) * _ =
    charge z.1 * ((single z).paint (subject A (owner z.1) t) * _)
  exact mul_assoc _ _ _

theorem height (z:Index owner grades T) :
    (M z).height σ=(1+‖charge z.1‖)*(single z).height σ := by
  change ((1+‖charge z.1‖)*(single z).salary) *
     Real.exp (σ*((joint sites (owner z.1)).length+(single z).atom.length:ℕ)) =
    (1+‖charge z.1‖)*((single z).salary *
     Real.exp (σ*((home sites (owner z.1)).length+(single z).atom.length:ℕ)))
  simp only [joint,home,WilsonOriginalStarSceneRows.length,mul_assoc]

theorem honored (z:Index owner grades T) (paid:(single z).Budget) : (M z).Budget := by
  intro t
  change ‖charge z.1*(single z).paint (subject A (owner z.1) t)‖≤(1+‖charge z.1‖)*(single z).salary
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (paid _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (by linarith) (single z).sound.le)

end YM.Integration.WilsonOriginalPointCompactRoster
