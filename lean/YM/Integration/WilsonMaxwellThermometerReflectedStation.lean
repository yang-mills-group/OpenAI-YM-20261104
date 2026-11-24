import YM.Integration.WilsonMaxwellThermometerReflectedPhysicalColumns
import YM.Integration.WilsonPositionProgramOriginalStationMenu
import YM.Integration.WilsonPositionProgramReflectedRead
import YM.Integration.WilsonPositionThermometerStationUnit
/-! The two separated reflected energy readings on their own inverse-tuned
original fields, including the literal cutoffs of both proper means. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedStation
open Filter Function Set Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open Labels XSpace XSpace.Normalize Maxwell Maxwell.Free Source Climb Table Trace Trace.Pilot
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMaxwellThermometerReflectedPhysicalColumns (height levels active atCut)
open WilsonPositionThermometerCapStation (Group index)
open WilsonMaxwellThermometerReflectedIncidence (site Pair mass)
open private separate from YM.Integration.WilsonPositionProgramReflectedPurse
open scoped Topology BigOperators Classical

variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
abbrev Name:=Bool × (Fin 2→Bool) × Finset (Fin 2)
def phase (n:Name)(i:Fin 2):ℂ →L[ℝ] ℝ:=
  if i∈n.2.2 ∧ n.2.1 i then Complex.imCLM else Complex.reCLM

theorem vacancy (A:Group R.family 6)(checked:A.station.checked f H A.horizon)
    (fixed:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j):
    ∀ᶠ z:ℕ×ℕ in f.fuse,∀(a:Axis)(b:Sec G 6)(n:Name)(i:Fin 2),i∉n.2.2 →
      atCut R A a b n.1 n.2.2 z.1 z.2 i=R.family.book.scalar (levels i) ∧
      ∀o:Site (R.family.side z.1 z.2),R.family.O z.1 z.2
        (atCut R A a b n.1 n.2.2 z.1 z.2 i) o=1:=by
  have booked (i:Fin 2):=WilsonPositionThermometerStationUnit.original A.station (index A (height i)) R.makes checked
  filter_upwards [eventually_all.mpr booked] with z paid
  intro a b n i missing
  have unit:(fields R.family.labels _).symm (leaf G (height i))=(Bel R.family.book).unit (height i):=by
    apply Free.address_inj R.family.labels _
    rw [Free.address_eval,LinearEquiv.apply_symm_apply,Free.unit_address]
    rfl
  rw [atCut,active,WilsonMaxwellThermometerReflectedPhysicalColumns.tag,if_neg missing,unit,fixed]
  exact paid i

variable {D k u e:ℕ}(d:Fin 2→ℕ)(fit:∀i,levels i<d i)
local notation "Q" => deck (G:=G) levels d fit
def source (A:Group R.family 6)(a:Axis)(b:Sec G 6)(m:ℕ)(n:Name)(N p:ℕ):Herit Q:=
  WilsonMaxwellThermometerReflectedPhysicalColumns.issued R d fit A a b n.1 n.2.2 m N p (phase n)
def difference (big:0<D)(φ:Wilt Q)(A:Group R.family 6)(checked:A.station.checked f H A.horizon)
    (a:Axis)(b:Sec G 6)(m N p k:ℕ)(n:Name)(t:ℕ)(v:Alma ((primes G).F 0)):ℝ:=
  WilsonPositionProgramOriginalStationMenu.difference R (fun _:Name=>1) (fun _=>levels) (fun _=>d)
    (fun _=>fit) big (fun _=>φ) A checked m N p N p k (source R d fit A a b m) n t v

/-- One smooth mass and the same physical coordinates across both chiralities and
every retained proper face. The last limit takes UV at each fixed physical period. -/
theorem original (simple:G.Simple)(reading:RG05Preconstruction.ReadoutPurchase R.b)
    (funded:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(cap:capP Q ≤ k)
    (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a):
    ∃φ:Wilt Q,WilsonPositionProgramReflectedRead.reading Q a φ=mass a x B ∧
      ∀ᶠ m:ℕ in atTop,1≤zz R.family.path.levels m → ∀A:Group R.family 6,A.station.k=m →
        ∀checked:A.station.checked f H A.horizon,∀b:Sec G 6,∀(n:ℕ×ℕ→Name)
        (t:ℕ×ℕ→Fin (e+1))(v:ℕ×ℕ→Alma ((primes G).F 0)),
          Tendsto (fun j:ℕ×ℕ=>difference R d fit big φ A checked a b m j.2 j.1 k (n j) (t j) (v j))
            ((atTop:Filter ℕ).curry atTop) (𝓝 0):=by
  obtain ⟨φ,field,_,_⟩:=WilsonPositionProgramReflectedPurse.original Q a x B 1
  have seen:WilsonPositionProgramReflectedRead.reading Q a φ=mass a x B:=by
    funext w
    unfold WilsonPositionProgramReflectedRead.reading
    rw [field 0,field 1]
    exact WilsonPositionProgramReflectedRead.sample a x B w.1 w.2
  have apart (i j:Fin 2)(ne:i≠j):Disjoint (tsupport (φ i).ψ.val) (tsupport (φ j).ψ.val):=by
    simp only [field]
    fin_cases i <;> fin_cases j
    · exact (ne rfl).elim
    · exact separate a x B
    · exact (separate a x B).symm
    · exact (ne rfl).elim
  refine ⟨φ,seen,?_⟩
  filter_upwards [WilsonPositionProgramOriginalStationMenu.ordered (c:=6) (f:=f) (H:=H) R
      (fun _:Name=>1) (fun _=>levels) (fun _=>d) (fun _=>fit) simple reading funded big rails
      (fun _=>cap) (fun _=>φ) (fun _=>apart),
    WilsonMaxwellThermometerReflectedPhysicalColumns.original (f:=f) (H:=H) R simple 1 zero_lt_one e d fit] with m board wage
  intro strip A date checked b n t v
  let costs (s:Name)(i:Fin 2):ℝ:=
    let F:=R.family.labels.level (levels i)
    (Fintype.card (Alma F)*(e+1:ℕ):ℕ)*(‖phase s i‖ *
      ((2:ℝ)^(univ.sup fun w:F.Index=>(F.grades w).2)*R.family.path.levels.clock.hatBeta m^((1:ℝ))*
        (WilsonPositionThermometerStationNorm.cost R.family (levels i)*‖active R A a b s.1 s.2.2 i‖)))
  exact board strip A date checked (source R d fit A a b m) costs
    (fun s N p top i=>wage A date checked N p top a b s.1 s.2.2 (phase s) i) n t v

end YM.Integration.WilsonMaxwellThermometerReflectedStation
