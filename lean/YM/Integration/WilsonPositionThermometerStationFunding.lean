import YM.Integration.WilsonPositionThermometerStationTransport
import YM.Integration.NativePreselectedPostnumericPeriodRun

/-! Buy the true primary-column cost before the common block length is chosen.
Each original sheet gets one fixed floor. Its decreasing stage exponent pays
all later finite extraction accuracies on the same run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationFunding
open Function Set Filter Lattice RG Wilson RG.Supply Precision Push.PriceCompiler
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.R2I.RG05Joint
open MergeProof.East Next.UVStress Climb
open scoped Classical Topology
universe u
variable {G : Gauge}

private theorem bought (s : Sheet G) (j : ℕ) : ∃ n : ℕ, ∀ L ≥ n,
    (s.profile j).columns ≤ (L:ℝ)^((j:ℝ)+1)⁻¹ :=
  eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < ((j:ℝ)+1)⁻¹) |>.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (s.profile j).columns)

def floor (s : Sheet G) (j : ℕ) : ℕ := (bought s j).choose

variable (Demand : Sheet G → MapPrices → Type u)
variable (extra : ∀ s q, Demand s q → ℕ → ℕ)
variable (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
variable (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
variable (R : Run G)

def combined (s : Sheet G) (q : MapPrices) (w : Demand s q) : ℕ → ℕ :=
  max (extra s q w) (floor s)

/-- The augmented column floor preserves every original forecast of the
existing election on exactly this run. -/
theorem previous (paid : PostnumericPreselection Demand (combined Demand extra) numeric postnumeric R) :
    PostnumericPreselection Demand extra numeric postnumeric R := by
  obtain ⟨s,q,w,n,before,floorPaid,rest⟩ := paid
  exact ⟨s,q,w,n,before,fun j => (le_max_left _ _).trans (floorPaid j),rest⟩

theorem original (paid : PostnumericPreselection Demand (combined Demand extra) numeric postnumeric R)
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ i ≥ m, (R.family.path.levels.params (i+1)).columns ≤
      ((R.family.S.block i).val : ℝ)^ε := by
  obtain ⟨s,q,w,n,hbase,hfloor,hsheet,hK,prices⟩ := paid
  let C := R.family
  let J (i : ℕ) := C.path.levels.clock.J (i+1)
  have checked (i : ℕ) : (C.path.levels.params (i+1)).columns ≤
      ((C.S.block i).val : ℝ)^((J i:ℝ)+1)⁻¹ := by
    let j := J i
    have hs : (C.path.levels.params (i+1)).columns = (R.metals.p.profile j).columns :=
      congrArg (fun x => x.columns) (params_eq R.alloy.B.valid (i+1))
    have source : (R.metals.p.profile j).columns = (s.profile j).columns := by rw [hsheet]
    have bound : n j ≤ (R.rolls.L j).val := by
      have spec := (R.rolls.large j).need
      have eqn : R.metals.p.floorL j = n j := by rw [hsheet]
      exact eqn ▸ spec
    have enough : floor s j ≤ (R.rolls.L j).val :=
      (le_max_right (extra s q w j) (floor s j)).trans ((hfloor j).trans bound)
    have scale : C.S.block i = R.rolls.L j := block_eq R.alloy.B.valid i
    rw [hs, source, scale]
    exact (bought s j).choose_spec _ enough
  have stages : Tendsto J atTop atTop := C.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)
  have tends : Tendsto (fun i => ((J i:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    ((tendsto_natCast_atTop_atTop.comp stages).atTop_add (tendsto_const_nhds (x:=(1:ℝ)))).inv_tendsto_atTop
  obtain ⟨b,hb⟩ := eventually_atTop.1 (tends.eventually (ge_mem_nhds he))
  filter_upwards [eventually_ge_atTop b] with m hm i hi
  exact (checked i).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (C.S.block i).property)
    (hb i (hm.trans hi)))

/-- All cutoffs and all periods use their actual station column after one
common pre-length purchase. The reference column is the signed microscopic
one on the selected original station. -/
theorem filed (paid : PostnumericPreselection Demand (combined Demand extra) numeric postnumeric R)
    (d : ℕ) (ε : ℝ) (he : 0 < ε) : ∀ᶠ m : ℕ in atTop, ∀ D (V : Vane R.family D)
    (j : Fin (D+1)), j.val = d → ∀ (w : (Bel R.family.book).Field j) N per,
    m ≤ V.k → V.k ≤ N →
    let v := V.wheel.atCut (N,per) j w
    (R.family.labels.level j).coeffSize (Next.Rank.Price.awake R.family j m N per v) ≤
      (R.family.S.a m / R.family.S.a V.k)^ε *
        (R.family.labels.level j).coeffSize (Next.Rank.Price.awake R.family j V.k N per v) := by
  filter_upwards [original Demand extra numeric postnumeric R paid ε he,
    eventually_ge_atTop (R.family.ref d)] with m stages href D V j hj w N per live upper
  apply WilsonPositionThermometerStationTransport.filed R.family V j w R.makes (hj.symm ▸ href) live upper ε
  exact fun i hi _ => stages i hi

end YM.Integration.WilsonPositionThermometerStationFunding
end
