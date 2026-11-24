import YM.OPE.Exchange.Coherence
import YM.OPE.Orbits.Continuity

/-!
# rc readout against center-and-exterior tests away from contacts

Full finite test detector on the EXACT continuum `Field`; charges only a fixed constant at a
fixed output horizon. Not a block-k norm of an RG germ. Include center test variable (need for
cutoff passage). Relative supports eventually have the required uniform geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Profile
open MeasureTheory Function Filter Set OPE Orbits Table
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {n : ℕ}

-- Centering policy (inputs may include the center position; not an extra insertion on that side!)
def liftAt (s:ℝ)(x:Points n)(o:E4): Fin n→ E4:= fun i=> s • x i + o

def venue (X:Set (Points n)) (M η:ℝ):= ∀ x∈X, WithinRoom 1 M η x.ofLp (0:E4)

-- arbitrary arity, cf. compact_separation Contacts.Anchor
lemma finite_distances (K : Set (Points n))(hc : IsCompact K)(hx : K ⊆ conf _):∃ η : ℝ,0<η ∧ ∀ x∈K,∀ i j:Fin n,i≠j→η ≤ ‖x i-x j‖ := by
  have hp(i j:Fin n):∃ u : ℝ,0<u ∧ ∀ p∈ K,i≠j → u ≤ ‖p i-p j‖:=by
    by_cases he:i=j; · exact ⟨1,one_pos,fun _ _ h=>(h he).elim⟩
    by_cases ht:K.Nonempty;swap; · exact ⟨1,one_pos,fun x h _=>(ht ⟨x,h⟩).elim⟩
    obtain ⟨p,hp,hm⟩:= hc.exists_isMinOn ht (f:=fun x:Points n=>‖x i-x j‖) (by fun_prop)
    exact ⟨_,norm_pos_iff.mpr <| sub_ne_zero_of_ne ((hx hp).ne he),fun x h _=>hm h⟩
  choose a ha h using hp
  obtain ⟨u,hu,hu'⟩:= ((show ∀ᶠ v in 𝓝[>] (0:ℝ),0<v from self_mem_nhdsWithin).and (show ∀ᶠ v in 𝓝[>] (0:ℝ),∀ i j,v ≤ a i j from eventually_all.mpr fun i=> eventually_all.mpr fun j=> Eventually.filter_mono nhdsWithin_le_nhds (ge_mem_nhds (ha i j)))).exists
  exact ⟨u,hu,fun x hx i j h' =>(hu' i j).trans (h i j x hx h')⟩

lemma finite_venue {X:Set (Points n)} (hc:IsCompact X) (he:X ⊆ conf _) : ∃ M η : ℝ,0≤ M ∧ 0<η ∧ venue X M η := by
  obtain ⟨η,hη,h⟩:=finite_distances X hc he
  have hImage := hc.image (f:= fun x:Points n=>x.ofLp) (by fun_prop)
  obtain ⟨M,hm⟩:= hImage.isBounded.exists_norm_le
  refine ⟨max 0 M,η,le_max_left ..,hη, fun x hx => ⟨fun i=> ?_,fun i j hij=> ?_⟩⟩
  · simp only [mul_one,sub_zero]; exact (norm_le_pi_norm x.ofLp i|>.trans (hm _ ⟨_,hx,rfl⟩)).trans (le_max_right ..)
  simpa only [mul_one] using h x hx i j hij

lemma around (x:Points n)(r:ℝ)(o:E4){M η:ℝ}(hr:0 ≤ r)(h:WithinRoom 1 M η x.ofLp (0:E4)): WithinRoom r M η (liftAt r x o) o:= by
  constructor
  · intro i; simpa only [liftAt,add_sub_cancel_right,norm_smul,Real.norm_of_nonneg hr,mul_comm M] using! mul_le_mul_of_nonneg_left (by simpa only [sub_zero,mul_one] using h.span i) hr
  intro i j hij
  simpa only [liftAt,add_sub_add_right_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg hr, mul_comm η] using! mul_le_mul_of_nonneg_left (by simpa only [mul_one] using h.spaced i j hij) hr

lemma finite_clears (K:Set (Points (n+1))) (hc:IsCompact K)(hx:K ⊆ conf _) :∃ c:ℝ,0<c ∧ ∀ y∈K, ClearOf (y 0) (fun j:Fin n=>y j.succ) c := by
  obtain ⟨η,hη,h⟩:=finite_distances K hc hx
  exact ⟨_,hη,fun x h'=>⟨fun i=>h x h' 0 _ (Fin.succ_ne_zero i).symm,fun i j hij=>h x h' _ _ ((Fin.succ_injective _).ne hij)⟩⟩

-- Mass for the **last** profile integration; for RG use actual demand seminorm instead
-- (readout theorem monotone in profile price). Keep profile derivative costs there.
def mass1 (t:Test n) : ℝ := ∫ x:Points n, ‖t x‖

lemma mass1_nonneg (t:Test n) : 0≤ mass1 t := integral_nonneg fun _=> norm_nonneg _

variable {G:Gauge}{L:Register G} {S T : Table L}

-- fixed exteriors (including NONE at arity n=0); center-and-point test.
structure Probe (S:Table L) where
  n : ℕ
  e : Fin n→ℕ
  fields : ∀ j,S.Field (e j)
  shape : Test (n+1)

namespace Probe
variable (U: Probe S)

def directly (T:Table L)(U:Probe S)(x:S.Field n) := U.shape.applyTo fun y:Points (U.n+1) => upon T n (y 0) (fun j:Fin U.n=> y j.succ) U.fields x

lemma rel (y:Points (n+1)) : Points.cons (y 0) (Points.tail y)=y := by
  ext1 i; refine i.cases ?_ (fun j=>?_); all_goals rfl

lemma as_upon (T:Table L)(p : Exterior L) (h:T.Hierarchy) (hh:T.respects S) (x:S.Field n) :
    let o:E4:=p.point 0; let y:=Points.tail p.point
    T.read p.point (Fin.cons ⟨n,S.representative n x⟩ p.letter) = upon T n o y.ofLp (Orbits.fields S p) x:=by
  intro o y
  have hx : Points.cons o y=p.point := rel p.point
  have hi : Injective (beside (sole o) y.ofLp):=(consIn o y.ofLp (e:=Equiv.refl _)).mp (by change Points.cons o y∈_; rw [hx]; exact p.clear)
  change _=whole _ _ _ _ _
  let V : L.Token:=⟨n,S.representative n x⟩
  rw [whole_observed]; change _=OPE.observe _ _ (beside (sole V) _); rw [head_observe (e:=Equiv.refl _) ..]
  · change T.read p.point (Fin.cons V p.letter)= T.read (Points.cons o y) (Fin.cons V (Orbits.names (Orbits.fields S p)))
    rw [hx,← S.at_project T h.laws.toSymmetric hh p.clear,← S.at_project T h.laws.toSymmetric hh p.clear]; apply congr_arg (S.useAt T _)
    funext i; refine i.cases rfl (fun j=>?_); change S.classTokens (p.letter j)=⟨_,S.project _ (S.representative _ (S.project _ (p.letter j).snd))⟩
    rw [S.rep]
  exacts [h.laws.toSymmetric,hi]

lemma fitClear (y:Points (n+1))(h:y∈conf _) : Injective (beside (sole (y 0)) (fun k:Fin n=> y k.succ)) := (consIn (e:=Equiv.refl _) ..).1 (by change Points.cons (y 0) (Points.tail y)∈_; rw [rel]; exact h)

lemma leg_continuous (h:T.Hierarchy) (x:S.Field n) : ContinuousOn (fun y:Points (U.n+1) => upon T n (y 0) (fun j:Fin U.n=> y j.succ) U.fields x) (conf _):=by
  change ContinuousOn (fun y:Points (U.n+1)=> whole T (sole (y 0)) (sole x : Orbits.Labels S (fun _:Unit=>n)) (fun j:Fin U.n=>y j.succ) U.fields) _
  simp_rw [whole_observed]
  intro y hy
  let z(q:Points (U.n+1)) := beside (sole (q 0)) (fun j:Fin U.n=> q j.succ)
  refine ((OPE.smooth_observe T h.smooth _ (x:=z y) (fitClear y hy)).comp (f:=z) ((show Continuous z from ?_).continuousAt)).continuousWithinAt
  apply continuous_pi; rintro (i|j)
  · exact PiLp.continuous_apply _ _ _
  exact PiLp.continuous_apply _ _ _

def line (T:Table L)(U:Probe S)(h:T.Hierarchy)(n:ℕ) : S.Field n →ₗ[ℂ] ℂ where
  toFun:= directly T U
  map_add' x y:=by
    simp only [directly,Test.applyTo,map_add,mul_add]; apply integral_add (U.shape.smearing (U.leg_continuous h x)) (U.shape.smearing (U.leg_continuous h y))
  map_smul' c x:= by simp only [directly,Test.applyTo,map_smul,smul_eq_mul,RingHom.id_apply]; simp_rw [mul_left_comm (U.shape _) c]; rw [integral_const_mul]

lemma line_spans (h:S.Hierarchy) (x:S.Field n →ₗ[ℂ] ℂ) : ∃ B: Probe S→₀ℂ,Finsupp.linearCombination ℂ (fun U:Probe S=> line S U h n) B = x := by
  let f: Probe S → (S.Field n →ₗ[ℂ] ℂ):= fun U=>line S U h n
  let A:= Submodule.span ℂ (range f)
  have he: A.dualCoannihilator=⊥:=by
    apply le_bot_iff.mp; intro x hx; refine (Submodule.mem_bot ..).mpr ((S.faithfully n) ?_)
    rw [map_zero]
    obtain ⟨w,rfl⟩:= S.onto n x; ext1 p
    let q:=p.letter; let g := Fin.cons (α:=fun _=>L.Token) ⟨n,S.representative n (S.project n w)⟩ q
    have hv : EqOn (fun y : Points (_+1)=> S.read y g) 0 (conf _) := by
       apply Test.weak_null ((S.smooth_read h.smooth g).continuousOn)|>.mp
       intro t; let U:Probe S:= ⟨p.n,_,Orbits.fields S p,t⟩
       have ht:= (Submodule.mem_dualCoannihilator _).mp hx (f U) (Submodule.subset_span (Set.mem_range_self _))
       refine (Test.apply_eq t (P:=fun (y:Points (U.n+1))=>upon S n (y 0) (fun j:Fin U.n=>y j.succ) U.fields (S.project n w)) (fun x hx=> ?_)).trans ht
       exact as_upon _ ⟨p.n,x,q,hx⟩ h (fun _=>le_rfl) (S.project n w)
    exact calc
       _=S.spectra n (S.project n (S.representative n (S.project n w))) p:=by rw [S.rep]
       _=0:= hv p.clear
  have hp : A=⊤:=by rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=A),he]; simp
  exact LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination ..).trans hp) x

-- ACTUAL finite set of pilot profiles and ONE price. No bound allowed with geometry k below.
theorem tower (A:S.Hierarchy) (h:ℕ) : ∃ Q:Finset (Probe S), ∃ D:ℝ, 0 ≤ D ∧
    ∀ (a:S.Field h) r, 0 ≤ r→ (∀ j∈Q, ‖directly S j a‖ ≤ r) → ‖a‖ ≤ D*r :=by
  classical
  let K:= Fin (Module.finrank ℂ (S.Field h))
  let X:= Module.finBasis ℂ (S.Field h)
  choose H hH using fun i:K=> line_spans A (X.coord i)
  let μ(i:K):=∑ j∈(H i).support, ‖H i j‖
  let Q:=Finset.biUnion (Finset.univ:Finset K) fun i=> (H i).support
  refine ⟨Q,∑ i:K, μ i*‖X i‖, Finset.sum_nonneg fun i _=>mul_nonneg (Finset.sum_nonneg fun _ _=>norm_nonneg _) (norm_nonneg _),fun a r _ h=> ?_⟩
  nth_rw 1 [← X.sum_repr a]; rw [Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
  rw [mul_right_comm,norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  change ‖X.coord i a‖ ≤ _; rw [← hH i,Finsupp.linearCombination_apply]; simp only [Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply]
  unfold μ; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=> ?_)
  rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h j (Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ i,hj⟩)) (norm_nonneg _)
end Probe
end YM.RG17.Profile
