import YM.OPE.Therm.Press
import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineCharts
/-!
# Pressure events ROOM and PILOT

Canonical order weight on a set of faces. A seam witness replacement's
plaquette threshold will tolerate seeing all four seam links changed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.House
open Function Set Filter RG Lattice Wilson MeasureTheory Cells SectorNext.Remainder.Affine
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge}(T:Tiling n) {U V : Config G n} {τ t:ℝ} {X Y:Finset (Edge (Site n))}
local notation "𝒞" => Config G n
local notation "E" => Edge (Site n)
local notation "η" => prior G n
local notation "F" => Face (Per n)
local notation "d" => Module.finrank ℝ G.Mat

def countables (v:T.Cell) : Finset F:= Finset.univ.filter (fun i=>touched i⊆suite T v)
def chilly (J:Finset F)(τ:ℝ) : Set 𝒞:= {U|∀ i∈J,G.chord (faceValue U i) ≤ τ}
def tape (J:Finset F)(τ:ℝ)(U:𝒞):ℝ:= if U∈chilly J τ then 1 else 0
def basins (Y:Finset E)(s:ℝ)(V:𝒞): Set 𝒞 := {U| ∀ i∈Y,G.chord (U i*(V i)⁻¹) ≤ s}
def towel (Y:Finset E)(s:ℝ)(V U:𝒞):ℝ:= if U∈basins Y s V then 1 else 0
lemma bath (J:Finset F): MeasurableSet (chilly (G:=G) J t):=by
   have ht : chilly (G:=G) J t= ⋂ i∈J, (trigger i t)ᶜ:=by ext U; simp [chilly,trigger,not_lt];
   rw [ht]; exact MeasurableSet.biInter (Finset.countable_toSet _) (fun i hi=> (fire_meas ..).compl)
lemma tape_env (J:Finset F): Envelope (tape (G:=G) J τ):= Envelope.piece (bath J) (Envelope.const _) (Envelope.const _)
lemma tapes {J K:Finset F}(U:𝒞) : tape (J∪K) τ U=tape J τ U * tape K τ U:=by
   have h: U∈ chilly (J∪K) τ ↔ U∈chilly J τ ∧ U∈ chilly K τ:= by simp only [chilly,Set.mem_setOf_eq,Finset.mem_union,or_imp, forall_and]
   unfold tape; simp_rw [h]; split_ifs <;> first|tauto|ring
lemma still_tape {J:Finset F} (h:∀ i∈J, Disjoint X (links (↑(touched i):Set _))): stills (G:=G) X (tape J t):=by
   intro U V hv; have he : U∈chilly J t ↔ V∈ chilly J t:= forall₂_congr fun i hi=> by
       have ht:faceValue U i=faceValue V i := by
           apply travel_local; refine fence_iff.mpr ?_; intro e he; apply hv; apply Finset.mem_compl.mpr; apply Finset.disjoint_right.mp (h i hi); obtain ⟨hp,hP⟩:= linn.mp he; exact linn.mpr ⟨List.mem_toFinset.mpr hp,List.mem_toFinset.mpr hP⟩
       rw [ht]
   unfold tape; simp_rw [he]
lemma cool_fence (v:T.Cell)(P:ℝ) : fence (G:=G) (fullRoom T v) (tape (countables T v) P) := by
   apply local_fence.mpr; intro U V h; let J:=countables T v; have he:U∈chilly J P↔ V∈chilly J P:= forall₂_congr fun i hi=> by -- same
       have ht:faceValue U i=faceValue V i:= by apply travel_local; exact agrees_mono h (fun x hx=> (show touched i ⊆suite T v from (Finset.mem_filter.mp hi).2) (List.mem_toFinset.mpr hx))
       rw [ht]
   change (if U∈chilly J P then _ else _)=(if V∈chilly J P then _ else _); simp_rw [he]
lemma cool_turn (h:T.kind=.site)(v:T.Cell)(U:𝒞) :
    pull (T.omega v) (T.translateBy v) U ∈chilly (countables T 0) τ ↔ U∈chilly (countables T v) τ:=by
   let s:=T.omega v; let b:=T.translateBy v; let f:=Face.send s b
   have hf (i:F): i∈countables T 0 ↔ f i∈countables T v:=by
      simp only [countables,Finset.mem_filter,Finset.mem_univ,true_and,f,Work.H03.touched_send,turnsSuite T h v]; have hv:= (Push.Local.turnSites s b).injective
      exact Iff.symm (Finset.image_subset_image_iff hv)
   have hp (i): G.chord (faceValue (pull s b U) i)= G.chord (faceValue U (f i)):= Face.send_price U i s b G.chord G.chord_inv (fun p q=> G.chord_conj q p)
   constructor
   · intro hx i hi; obtain ⟨i,rfl⟩:= Finite.injective_iff_surjective.mp (show Injective f from Face.injective_send s b) i
     rw [← hp]; exact hx i ((hf i).2 hi)
   exact fun hx i hi=> (hp i).trans_le (hx (f i) ((hf i).1 hi))
lemma cool_miss {P:Measure 𝒞}[IsFiniteMeasure P] (Z:ℝ)(h:∀ i:F,P.real (trigger i τ)≤ Z) (J:Finset F) : P.real ((chilly J τ)ᶜ) ≤ J.card*Z:=by
   rw [show (chilly J τ)ᶜ=⋃ i∈J,trigger (G:=G) i τ by ext U; simp only [chilly, Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_forall,mem_iUnion,SetLike.mem_coe,trigger]; push Not; simp only [not_le]] -- fix after
   exact ((measureReal_biUnion_finset_le (μ:=P) J (trigger · τ)).trans (Finset.sum_le_sum (fun i (_:i∈J)=> h i))).trans_eq (by simp)
section basin
private def setOfE (s:ℝ)(V:𝒞)(X:Finset E) (i:E) := if i ∈ X then (fun x: G.El=> x*(V i)⁻¹) ⁻¹' G.shell s else Set.univ
private lemma aspi (s:ℝ)(V:𝒞): basins X s V= Set.pi Set.univ (setOfE s V X):=by
   ext U; constructor
   · intro h i _; unfold setOfE; split; rename_i hi; exact h i hi; exact mem_univ _
   intro h i hi; have ht:= h i (mem_univ i); rw [setOfE,if_pos hi] at ht; exact ht
lemma basins_meas : MeasurableSet (basins X t U):=by
   rw [aspi]; apply MeasurableSet.univ_pi; intro i; unfold setOfE; split; exact (G.shell_meas t).preimage (measurable_id.mul_const _); exact MeasurableSet.univ
lemma towel_env : Envelope (towel X t U) := Envelope.piece basins_meas (Envelope.const _) (Envelope.const _)
lemma towel_fence : fence X (towel X t U):=by
   intro V W h; unfold towel
   have ht: V∈ basins X t U ↔ W∈basins X t U:= forall₂_congr fun i hi=> by rw [h (show i∈(X:Set _) from hi)] -- check
   simp_rw [ht]
lemma basin_eq (X:Finset E)(V:𝒞): (η).real (basins X t V)= (G.probHaar.real (G.shell t))^(X.card):=by
   unfold Measure.real prior
   rw [aspi, Measure.pi_pi]; let a:= G.probHaar (G.shell t); let D:=setOfE t V X; have hp i (hi:i∈X): G.probHaar (D i)= a:=by rw [show D i=_ from if_pos hi]; exact (measurePreserving_mul_right G.probHaar ((V i)⁻¹)).measure_preimage (G.shell_meas _).nullMeasurableSet -- fails show
   have hz i (hi:i∉X): G.probHaar (D i)=1:=by rw [show D i=_ from if_neg hi]; exact measure_univ
   have he : (∏ i:E,G.probHaar (D i))= a^X.card:= (Finset.prod_subset (Finset.subset_univ X) (by intro i _; exact hz i)).symm.trans (le_antisymm ?_ ?_) -- avoid
   · rw [show _= _ from he]; exact ENNReal.toReal_pow ..
   all_goals apply le_of_eq <;> try symm
   all_goals first | exact (Finset.prod_congr rfl hp).trans (by simp) | exact ((Finset.prod_congr rfl hp).trans (by simp)).symm
lemma lid (V:𝒞)(h:0<t)(he:t≤ 1) : Real.exp (- (X.card*d* Real.log (4/t))) ≤ ∫ U,towel X t V U∂η:=by
   rw [show towel X t V=(basins X t V).indicator (fun _=>1) from rfl,integral_indicator basins_meas,setIntegral_const,smul_eq_mul,mul_one,basin_eq];
   have ht:=pow_le_pow_left₀ (pow_nonneg (show 0≤ t/4 by positivity) d) (G.shell_ge t h he) X.card
   apply le_trans ?_ ht; refine le_of_eq ?_; rw [show Real.log (4/t)=-Real.log (t/4) by rw [← Real.log_inv]; congr 1; field_simp, mul_neg, neg_neg,mul_assoc,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (by positivity)] -- cast product!
end basin
lemma mellow (U V:𝒞)(he:∀ x:E,G.chord (U x*(V x)⁻¹)≤ t) (i:F): G.chord (faceValue U i) ≤ 4*t + G.chord (faceValue V i):=by
    let a:= faceValue V i; let b:= faceValue U i; have hf : G.chord (b*a⁻¹) ≤4*t := by convert travel_bound t (square i.2.val.1 i.2.val.2) i.1 U V (fun i _=> he i) using 1 <;> first| rfl | simp [square]
    exact le_trans (show G.chord b ≤ G.chord (b*a⁻¹)+G.chord a from (by simpa using G.chord_triangle (b*a⁻¹) a)) (add_le_add_left hf _)
lemma cleanEnough (h:U∈ basins (seam T) t V)(hu:0≤ t) (P:BudgetPoint)(hs:4*t+τ≤ P.threshold) (ht:∀ i, meld (seam T) V U∈chilly (countables T i) τ) : flags P.threshold U=∅:=by
    rw [Finset.eq_empty_iff_forall_notMem]; intro x he; obtain ⟨i,hi,hI⟩:= (flags_spec ..).mp he
    let W:=meld (seam T) V U; have he(x): G.chord (U x*(W x)⁻¹)≤ t:= by unfold W meld; split; rename_i he; exact h x he; rw [mul_inv_cancel, G.chord_one]; exact hu
    have hx:G.chord (faceValue W i)≤τ:= ht (T.which i.1) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,suite_front T i⟩); exact (not_lt_of_ge ((mellow U W he i).trans (le_trans (add_le_add_right hx _) hs))) hI
end YM.OPE.Therm.House
