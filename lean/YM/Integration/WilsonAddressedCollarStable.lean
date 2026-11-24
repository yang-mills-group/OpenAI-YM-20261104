import YM.RG05Readout.Aligned.Tune
import YM.FullVolume.Cross

/-! The measured return of one complete represented source on the selected
Wilson trajectory. The density includes the compulsory portfolio. The filed
primary stays on that trajectory and the entire compensated source has the
native gain even at an intermediate mesh. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarStable
open Lattice Wilson RG Push Bid Source Extra.Histories Extra.Histories.Relay
open RG05Readout RG05Readout.Aligned PhysicalNext.Repeat.Legato Bandage
open scoped Classical

variable {G : Gauge} (R : Run G) (simple : G.Simple)
set_option quotPrecheck false
local notation "C" => R.family
local notation "T" => (C).path

include simple in
theorem original {d N p : ℕ} (enrolled : (C).ref d ≤ N) :
    ∃ (M : Music ((C).labels.level d) (T) N p)
      (H : Committed (C) N p d R.w (waybill R.alloy.B.a) R.doors M),
    ∀ {w : ℕ} (_ : (C).ref d ≤ w) (_ : w ≤ N)
      (X : Coefficient ((C).labels.level d) ((C).side w p)) {t : ℝ}
      (_ : X.Format 0 (C).params ((T).rep N p w))
      (_ : X.remBound 0 ((T).rep N p w) (Real.sqrt ((T).levels.clock.forcedAllowance w)) t),
    let E := 4*(1+((T).levels.params w).columns)*(((C).labels.level d).coeffSize X.x+t)
    ∃ (S : ∀ i, Solo ((C).labels.level d) (T) p i),
      Pickup (C) M (waybill R.alloy.B.a) R.doors H w X t E S ∧
      ((S w).bar M 0).density 0 ((C).localSection d) ((T).rep N p w) =
        X.density 0 ((C).localSection d) ((T).rep N p w) ∧
      (∀ i, (C).ref d ≤ i → i < w → ∀ v,
        ((S i).bar M v).density 0 ((C).localSection d) ((T).rep N p i) =
          blast (T) N p i d (((S (i+1)).bar M v).density 0 ((C).localSection d) ((T).rep N p (i+1)))) ∧
      (((C).labels.level d).coeffSize ((M.tone w).index (S ((C).ref d)).a) ≤ 2*E) ∧
      ∀ (m u : ℕ), (C).ref d ≤ u → u ≤ w →
        let Q := dualize (T) N p M ((C).ref d) w S (-(S ((C).ref d)).a)
        (((C).S.a u)^d)⁻¹*(Q.cost u+((C).labels.level d).coeffSize (Q.voice u).x) ≤
          (((C).S.a m)^d)⁻¹*((C).S.a m/(C).S.a u)^d*E/gainChart (T) w u := by
  obtain ⟨M,H⟩ := committing (d:=d) (p:=p) (R.again simple).1.scrim enrolled
  refine ⟨M,H,?_⟩
  intro w hw live X t layout reserve
  dsimp only
  obtain ⟨S,record⟩ := picks H R.makes hw live layout reserve _ le_rfl le_rfl
  refine ⟨S,record,record.value R.makes,fun i lo hi v => record.transfer i lo hi v,
    record.size_bound R.makes,?_⟩
  intro m u lo hi
  let Q := dualize (T) N p M ((C).ref d) w S (-(S ((C).ref d)).a)
  let E := 4*(1+((T).levels.params w).columns)*(((C).labels.level d).coeffSize X.x+t)
  have paid : gainChart (T) w u*(Q.cost u+((C).labels.level d).coeffSize (Q.voice u).x) ≤ E :=
    record.expenses u lo hi
  have pos : 0 < gainChart (T) w u := Real.exp_pos _
  have rem := (le_div_iff₀ pos).2 ((mul_comm _ _).trans_le paid)
  have hm := pow_ne_zero d ((C).S.a_pos m).ne'
  have hu := pow_ne_zero d ((C).S.a_pos u).ne'
  have normalize : (((C).S.a m)^d)⁻¹*((C).S.a m/(C).S.a u)^d = (((C).S.a u)^d)⁻¹ := by
    rw [div_pow]; field_simp
  change (((C).S.a u)^d)⁻¹*(Q.cost u+((C).labels.level d).coeffSize (Q.voice u).x) ≤
          (((C).S.a m)^d)⁻¹*((C).S.a m/(C).S.a u)^d*E/gainChart (T) w u
  rw [normalize,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left rem (inv_nonneg.mpr (pow_nonneg ((C).S.a_pos u).le d))

end YM.Integration.WilsonAddressedCollarStable
