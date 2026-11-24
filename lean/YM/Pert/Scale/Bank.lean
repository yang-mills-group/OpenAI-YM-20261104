import YM.Pert.Scale.Circuit
import YM.Pert.Parity.Fields
/-! Graded engineering scaling on the *same* comparator labels, admissible as a position-frame matrix preserving lower horizons. Length (not inverse length) convention. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 700000
set_option maxRecDepth 2400
namespace YM.Pert.Scale
open Extra.FD Lattice RawLabels Labels Position Function Set Maxwell
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
def resizer (t : ℝ) (G : Gauge) (j) : Module.End ℝ (Taylor G j) := (t^(j+2)) • (LinearMap.id (R:=ℝ))

lemma stretch_commute (G : Gauge) (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (q : Pol G) (t : ℝ) :
   changed e (changed (resizer t G) q) = changed (resizer t G) (changed e q) := by
  apply eval_ext
  intro A
  simp only [eval_changed]; apply congrArg (fun A => Labels.read A q)
  funext i
  change t^(i+2) • (e i (A i)) = e i (t^(i+2) • (A i)); rw [map_smul]
lemma stretch_conj (q : Pol G) t : changed (resizer t G) (Labels.conjPol q) = Labels.conjPol (changed (resizer t G) q) := by
  apply eval_ext
  intro A; simp only [eval_changed,Labels.conj_value]
def grow (t : ℝ) (G : Gauge) (d : ℕ) : Labels.Label G d →ₗ[ℂ] Label G d where
  toFun p := ⟨changed (resizer t G) p.val,moved_limit p.property.1 _,fun A u=> by
    simp only [eval_changed,show changedJet (resizer t G) (colored u A) = colored u (changedJet (resizer t G) A) from funext fun i=> Eq.symm ((Taylor.paint u (j:=i)).map_smul (t^(i+2)) (A i))]
    exact p.property.2 ..⟩
  map_add' a b := Subtype.ext (map_add (changed _) a.val b.val)
  map_smul' r a := Subtype.ext (map_smul (changed _) r a.val)
variable {d : ℕ}
@[simp] lemma grow_unit (t : ℝ) : grow t G d (Labels.unit G d) = Labels.unit G d := Subtype.ext (map_one (changed _))
lemma grow_fixed (q : Label G d) t : fixedPolynomial G d (grow t G d q) = grow t G d (fixedPolynomial G d q) := Subtype.ext (stretch_commute G _ q.val t)
def gear (F : Frames G) (d : ℕ) (t : ℝ) := enroll F d ∘ₗ grow t G d ∘ₗ physicalLabel F d
variable (F : Frames G) (p : Full.Source (Frame:=F) d)
lemma gear_def (t:ℝ) : gear F d t p = enroll F d (grow t G d (physicalLabel F d p)) := rfl
lemma gear_lifts (t : ℝ) : physicalLabel F d (gear F d t p)=grow t G d (physicalLabel F d p) := by
  have hf : fixedPolynomial G d (physicalLabel F d p)=physicalLabel F d p := by rw [←embed_round F (physicalLabel F d p),physical_round]
  rw [gear_def,embed_round,grow_fixed,hf]
lemma gear_unit (t:ℝ) : gear F d t ((freeTable F).unit d)=(freeTable F).unit d := by
  rw [gear_def,physical_unit,grow_unit];exact UVNext.FreeStress.pin_unit ..
lemma gear_spin (s : Ortho) (t:ℝ) : rideO F s d (gear F d t p) = gear F d t (rideO F s d p) := by
  have he : Function.Injective (physicalLabel F d) := fun a b h=>(physical_round F a).symm.trans ((congrArg (enroll F d) h).trans (physical_round F b))
  apply he
  rw [physical_ortho,gear_lifts, gear_lifts,physical_ortho]; exact Subtype.ext ((stretch_commute ..))
lemma gear_inherit (q : Label G d) (t:ℝ) : gear F d t (enroll F d q) = enroll F d (grow t G d q) := by simp only [gear_def,embed_round,← grow_fixed, enroll_fixed]
lemma gear_conj (t:ℝ) : (freeTable F).conj (table_spin F) d (gear F d t p)= gear F d t ((freeTable F).conj (table_spin F) d p) := by
  have he : Injective (physicalLabel F d) := fun a b h=>(physical_round F a).symm.trans ((congrArg (enroll F d) h).trans (physical_round F b)); apply he
  rw [physical_real,gear_lifts,gear_lifts,physical_real]; exact Subtype.ext ((stretch_conj ..).symm)
lemma gear_lower {j} (hj : p∈lower F j d) (t : ℝ) : gear F d t p∈lower F j d := by
  obtain ⟨a,rfl⟩ := hj
  let q : Label G d := ⟨a.val,a.property.2⟩
  have h : (grow t G d q).val∈localFields G j := ⟨moved_limit a.property.1.1 _,(grow t G j ⟨_,a.property.1⟩).property.2⟩
  refine ⟨⟨_,show (grow t G d q).val∈ (localFields G j ⊓ localFields G d) from ⟨h,(grow t G d q).property⟩⟩,(gear_inherit F q t).symm⟩

/-- Length-frame increment from the identity in the allowed finite real buffer. -/
def bank (F : Frames G) (d : ℕ) (t : ℝ) : Buffer F d :=
 ⟨((gear F d t - LinearMap.id).restrictScalars ℝ).toContinuousLinearMap,
   by
    refine ⟨?_,fun e _ p hp=>?_ ,fun p=>?_ ,fun s p=>?_ ,fun p=>?_⟩
    · exact (show gear F d t ((freeTable F).unit d) - _ = _ from by rw [gear_unit,sub_self])
    · exact Submodule.sub_mem _ (gear_lower F p hp t) hp
    · change (freeTable F).conj (table_spin F) d (gear F d t p - p) = _
      rw [map_sub,gear_conj]; rfl
    · change rideO F s.ortho d (gear F d t p - p) = _
      rw [map_sub,gear_spin]; rfl
    exact (gear F d t - LinearMap.id).map_smul _ _
 ⟩
lemma motor_bank (t : ℝ) : motor F (bank F d t) p = gear F d t p := by
   change p + (gear F d t p - p)=_
   abel

lemma alg_match (t : ℝ) : changed (resizer t G)= MvPolynomial.aeval (fun i => ((t:ℂ)^Labels.generation i) • MvPolynomial.X i) := by
  apply MvPolynomial.algHom_ext
  intro i
  have he := eval_ext (changed (resizer t G) (MvPolynomial.X i)) (((t:ℂ)^Labels.generation i)• MvPolynomial.X i) fun A=>by
     rw [eval_changed,Labels.read, MvPolynomial.aeval_X,map_smul,Labels.read,MvPolynomial.aeval_X]
     simp only [Labels.coord,changedJet, resizer, LinearMap.smul_apply, LinearMap.id_coe, id_eq,map_smul,generation, Finsupp.smul_apply,smul_eq_mul, Complex.ofReal_mul,Complex.ofReal_pow]
  rw [MvPolynomial.aeval_X]
  exact he
lemma grow_weights {p : Label G d} {w : ℕ} (hp : (p.val).IsWeightedHomogeneous generation w) (t : ℝ) : grow t G d p=((t:ℂ)^w) • p := Subtype.ext (by
  change changed (resizer t G) p.val = ((t:ℂ)^w) • p.val
  generalize hx : p.val = q at hp ⊢
  have hk : ∀ (q:Pol G), q.IsWeightedHomogeneous generation w → changed (resizer t G) q=((t:ℂ)^w) • q := fun q hh => by
    induction hh using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ia ib => simp only [map_add,ia,ib,smul_add]
    | monomial b c hb =>
       rw [alg_match, MvPolynomial.aeval_monomial]
       rw [← Algebra.smul_def]
       change c • (∏ i∈ b.support, ((((t:ℂ)^generation i) • (MvPolynomial.X i : Pol G))^(b i))) = _
       simp_rw [smul_pow, Finset.prod_smul, ←pow_mul, Finset.prod_pow_eq_pow_sum, smul_comm c]
       rw [show (∑ i ∈ b.support, generation i*b i)=w by simpa only [Finsupp.weight_apply,Finsupp.sum, smul_eq_mul, mul_comm] using hb]
       rw [show ∏ i∈b.support, (MvPolynomial.X i : Pol G) ^ b i = _ from Eq.symm (MvPolynomial.monic_monomial_eq b),← (MvPolynomial.monomial b).map_smul]; simp only [smul_eq_mul,mul_one]
  exact hk q hp)

end YM.Pert.Scale
