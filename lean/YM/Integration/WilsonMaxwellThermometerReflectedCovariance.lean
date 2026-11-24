import YM.Integration.WilsonMaxwellThermometerReflectedStationBounds
import YM.Integration.WilsonMaxwellThermometerIndependentReflection
/-! Ordered removal of both regulators in the full centered first derivative
of each inverse-tuned reflected pair. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedCovariance
open Filter Function Set Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Cadenza
open Source Source.Drops Labels XSpace XSpace.Normalize Maxwell Table Climb Trace Trace.Pilot
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels active)
open WilsonMaxwellThermometerReflectedStation (Name phase source)
open WilsonMaxwellThermometerReflectedStationBounds (originalTorus covered)
open WilsonMaxwellThermometerReflectedIncidence (site mass)
open WilsonMaxwellThermometerIndependentReflection (pair)
open WilsonMaxwellThermometerReflectedSources (signs)
open WilsonPositionThermometerCapStation (Group)
open WilsonNeutralCopiedField (point)
open private separate from YM.Integration.WilsonPositionProgramReflectedPurse
open scoped Topology BigOperators Classical

private theorem negligible {I:Type}{L:Filter I}{a b:I→ℝ}{C:ℝ}
    (decay:Tendsto a L (𝓝 0))(room:∀ᶠ i in L,‖b i‖≤C):
    Tendsto (fun i=>a i*b i) L (𝓝 0):=by
  have bound : ∀ᶠ i in L, ‖a i*b i‖ ≤ ‖a i‖*C :=room.mono fun i hi=>by
    rw [norm_mul];exact mul_le_mul_of_nonneg_left hi (norm_nonneg (a i))
  exact squeeze_zero_norm' bound (by simpa using decay.norm.mul_const C)

private theorem paired {I:Type}{L:Filter I}(F Q:I→Finset (Fin 2)→ℕ→ℝ)
    (cut:∀s,∀t≤1,Tendsto (fun j=>F j s t-Q j s t) L (𝓝 0))
    {C:ℝ}(bounded:∀s,∀t≤1,∀ᶠ j in L,‖Q j s t‖≤C):
    Tendsto (fun j=>pair (F j)-pair (Q j)) L (𝓝 0):=by
  have product (s r:Finset (Fin 2))(t u:ℕ)(ht:t≤1)(hu:u≤1):
      Tendsto (fun j=>F j s t*F j r u-Q j s t*Q j r u) L (𝓝 0):=by
    have a:=cut s t ht
    have b:=cut r u hu
    have h: Tendsto (fun j=>(F j s t-Q j s t)*(F j r u-Q j r u)+
        (F j s t-Q j s t)*Q j r u+(F j r u-Q j r u)*Q j s t) L (𝓝 0):=by
      simpa using ((a.mul b).add (negligible a (bounded r u hu))).add (negligible b (bounded s t ht))
    convert h using 1
    funext j;ring
  have h:=((cut univ 1 le_rfl).sub (product {0} {1} 1 0 le_rfl zero_le_one)).sub
    (product {0} {1} 0 1 zero_le_one le_rfl)
  convert h using 1
  · funext j;unfold pair;ring
  · simp

variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{D k u e:ℕ}
variable (d:Fin 2→ℕ)(fit:∀i,levels i<d i)
local notation "Q" => deck (G:=G) levels d fit
def current (T:Name→ℕ→ℝ)(s:Bool):ℂ:=
  ∑y:Fin 2→Bool,signs y*(pair (fun S t=>T (s,y,S) t):ℂ)

theorem filed (simple:G.Simple)(readout:RG05Preconstruction.ReadoutPurchase R.b)
    (funded:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1≤e)(cap:capP Q ≤ k)(φ:Wilt Q)
    (apart:∀i j,i≠j → Disjoint (tsupport (φ i).ψ.val) (tsupport (φ j).ψ.val)):
    ∀ᶠ m:ℕ in atTop,1≤zz R.family.path.levels m → ∀A:Group R.family 6,A.station.k=m →
      ∀checked:A.station.checked f H A.horizon,∀(a:Axis)(b:Sec G 6)(s:Bool),
        Tendsto (fun w:ℕ×ℕ=>
          current (fun n t=>originalTorus R d fit φ A checked a b m w.2 w.1 D n t (point ((primes G).F 0) 0)) s-
          current (fun n t=>covered R d fit big φ A checked a b m w.2 w.1 k n t (point ((primes G).F 0) 0)) s)
          ((atTop:Filter ℕ).curry atTop) (𝓝 0):=by
  filter_upwards [WilsonPositionProgramOriginalStationMenu.ordered (c:=6) (f:=f) (H:=H) R
      (fun _:Name=>1) (fun _=>levels) (fun _=>d) (fun _=>fit) simple readout funded big rails
      (fun _=>cap) (fun _=>φ) (fun _=>apart),
    WilsonMaxwellThermometerReflectedPhysicalColumns.original (f:=f) (H:=H) R simple 1 zero_lt_one e d fit,
    WilsonMaxwellThermometerReflectedStationBounds.original (f:=f) (H:=H) R d fit simple funded big rails cap φ apart]
    with m board wage room
  intro strip A date checked a b s
  let money(n:Name)(i:Fin 2):ℝ:=
    let F:=R.family.labels.level (levels i)
    (Fintype.card (Alma F)*(e+1:ℕ):ℕ)*(‖phase n i‖ *
      ((2:ℝ)^(univ.sup fun v:F.Index=>(F.grades v).2)*R.family.path.levels.clock.hatBeta m^((1:ℝ))*
        (WilsonPositionThermometerStationNorm.cost R.family (levels i)*‖active R A a b n.1 n.2.2 i‖)))
  have seen:=board strip A date checked (source R d fit A a b m) money
    (fun n N per top i=>wage A date checked N per top a b n.1 n.2.2 (phase n) i)
  obtain ⟨C,_,cost⟩:=room strip A date checked a b
  let pix:=point ((primes G).F 0) 0
  let finrow (w:ℕ×ℕ)(n:Name)(t:ℕ):=originalTorus R d fit φ A checked a b m w.2 w.1 D n t pix
  let covrow (w:ℕ×ℕ)(n:Name)(t:ℕ):=covered R d fit big φ A checked a b m w.2 w.1 k n t pix
  let Λ:Filter (ℕ×ℕ):=(atTop:Filter ℕ).curry atTop
  have late:∀ᶠ w in Λ,m<w.2:=eventually_curry_iff.mpr (Eventually.of_forall fun _=>eventually_gt_atTop m)
  have term(y:Fin 2→Bool):Tendsto (fun w=>signs y*((pair (fun S t=>finrow w (s,y,S) t):ℝ):ℂ)-
      signs y*((pair (fun S t=>covrow w (s,y,S) t):ℝ):ℂ)) Λ (𝓝 0):=by
    have h:=paired (fun w S t=>finrow w (s,y,S) t) (fun w S t=>covrow w (s,y,S) t)
      (fun S t ht=>seen (fun _=>(s,y,S)) (fun _=>⟨t,Nat.lt_succ_of_le (ht.trans he)⟩) (fun _=>pix))
      (fun S t ht=>late.mono fun w top=>cost _ _ top (s,y,S) t (ht.trans he) pix)
    simpa only [Function.comp_apply,Complex.ofReal_sub,Complex.ofReal_zero,mul_sub,mul_zero] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp h).const_mul (signs y)
  have total:=tendsto_finsetSum univ (fun y _=>term y)
  simpa only [current,Finset.sum_sub_distrib,Finset.sum_const_zero,finrow,covrow,pix,Λ] using total

theorem original (simple:G.Simple)(readout:RG05Preconstruction.ReadoutPurchase R.b)
    (funded:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1≤e)(cap:capP Q ≤ k)
    (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a):
    ∃φ:Wilt Q,WilsonPositionProgramReflectedRead.reading Q a φ=mass a x B ∧
    ∀ᶠ m:ℕ in atTop,1≤zz R.family.path.levels m → ∀A:Group R.family 6,A.station.k=m →
      ∀checked:A.station.checked f H A.horizon,∀(b:Sec G 6)(s:Bool),
        Tendsto (fun w:ℕ×ℕ=>
          current (fun n t=>originalTorus R d fit φ A checked a b m w.2 w.1 D n t (point ((primes G).F 0) 0)) s-
          current (fun n t=>covered R d fit big φ A checked a b m w.2 w.1 k n t (point ((primes G).F 0) 0)) s)
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
  filter_upwards [filed (f:=f) (H:=H) R d fit simple readout funded big rails he cap φ apart] with m sale
  intro strip A date checked b s
  exact sale strip A date checked a b s
end YM.Integration.WilsonMaxwellThermometerReflectedCovariance
