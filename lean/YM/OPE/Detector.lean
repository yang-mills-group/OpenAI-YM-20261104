import YM.OPE.Frame
import YM.Dash.Regular
import YM.Euclid.OtherPlanes
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Exact finite readout at a fixed center of the physical hierarchy
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Set Analysis
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} (S T : Table L) {n : ℕ}

/-- Exterior word, represented by a list with the actual physical Tags. May
include the empty word. -/
abbrev ExteriorData (S : Table L) := Table.ClassWords S

def detectorRaw (q : S.Tag) : L.Token := ⟨q.1,S.representative q.1 q.2⟩
@[simp] lemma raw_class (q : S.Tag) : S.classTokens (detectorRaw S q) = q := by
  obtain ⟨d,x⟩ := q
  change Sigma.mk d (S.project d (S.representative _ x))=Sigma.mk d x
  rw [S.rep]

def classes (l : Fin n → S.Tag) (x : Points n) : ExteriorData S := List.ofFn fun i=> (x i,l i)

def positions (E : ExteriorData S) : Points E.length := points fun i => (E.get i).1
def tags (E : ExteriorData S) (i : Fin E.length) := (E.get i).2

def ordinary (E : ExteriorData S) : L.Word := List.map (fun p : E4 × S.Tag => (p.1,detectorRaw S p.2)) E

variable {S}

@[simp] lemma lifted_ordinary (E : ExteriorData S) : Table.ClassWords.lifted (ordinary S E)=E := by
  rw [ordinary,Table.ClassWords.lifted,List.map_map]
  simp only [Function.comp_def,raw_class]
  exact List.map_id'' (fun _=> Prod.mk.eta) E

/-- All coordinates different on the whole exterior including against the
origin; dense in the allowed (strict configuration) exterior geometries.
Using these as detectors does not identify any extra field classes. -/
def Apt (E : ExteriorData S) := Points.cons 0 (positions S E) ∈ generic _

def detectorTested (x : ExteriorData S) (E : ExteriorData S) := Table.ClassWords.read T (x ++ E)

/-- Testing one insertion at origin with fixed exterior. -/
def witnessAt (d : ℕ) (E : ExteriorData S) : Module.Dual ℂ (S.Field d) := LinearMap.comp
  (T.injectFront (fun i => detectorRaw S ((E.get i).2)) (Points.cons 0 (positions S E)) d) (S.representative d)

lemma witness_kernel {d} (q : S.Field d) (E : ExteriorData S) :
    witnessAt T d E q = S.useAt T (Points.cons 0 (positions S E)) (Fin.cons (⟨d,q⟩ : S.Tag) (tags S E)) := by
    let y := Fin.cons (α := fun _ : Fin (E.length+1) => S.Tag) ⟨d,q⟩ (tags S E)
    have he : detectorRaw S ∘ y = Fin.cons (⟨d,S.representative d q⟩: L.Token) (detectorRaw S ∘ tags S E) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp only [y,comp_apply,Fin.cons_zero,Fin.cons_succ,detectorRaw] <;> rfl
    change T.read _ _ = _; rw [show (fun i => detectorRaw S ((E.get i).2)) = detectorRaw S ∘ tags S E from rfl]
    rw [← he]
    rfl

lemma witness_value {d} (q : S.Field d) (E : ExteriorData S) : detectorTested T [(0,⟨d,q⟩)] E = witnessAt T d E q :=
    Table.ClassWords.via T _ _ rfl _ (Fin.cons ⟨d,q⟩ (tags S E)) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl) |>.trans (witness_kernel T q E).symm

lemma witness_classes {d} (q : S.Field d) (l : Fin n → S.Tag) (x : Points n) :
    witnessAt T d (classes S l x) q = S.useAt T (Points.cons 0 x) (Fin.cons ⟨d,q⟩ l) := by
  rw [← witness_value,detectorTested]
  apply Table.ClassWords.via _ _ (n+1) (by simp [classes])
  intro i; refine Fin.cases ?_ (fun j=> ?_) i
  · rfl
  change (classes S l x).get (Fin.cast (by simp [classes]) j) = (x j,l j)
  exact List.get_ofFn _ _ |>.trans (congr_arg (fun j=> (x j,l j)) (Fin.ext rfl))

lemma generic_across (x : Points n) (p : E4) : Points.across p x ∈ generic n ↔ x ∈ generic n := by
  simp only [mem_setOf_eq,generic,Function.Injective,Points.across_coord,PiLp.add_apply,add_left_inj]

lemma classes_apt (x : Points (n+1)) (hx : x∈generic _) (l : Fin n → S.Tag) :
    Apt (classes S l (Points.tail (Points.across (-(x 0)) x))) := by
  suffices he : Points.cons 0 (Points.tail (Points.across (-(x 0)) x)) ∈ generic (n+1) by
    have hgen {q : ℕ} {z : Points q} {l' : Fin q → S.Tag} (ha' : z ∈ generic _) :
        positions S (List.ofFn (fun i : Fin q => ((z i,l' i) : Table.Species S))) ∈ generic _ := by
      intro a' i j h
      have hi v := List.get_ofFn (fun i : Fin q => ((z i,l' i) : Table.Species S)) v
      have hv : (z (Fin.cast (by simp) i)) a'=(z (Fin.cast (by simp) j)) a' := by
        change ((List.get _ i).1:E4).ofLp a' = ((List.get _ j).1:E4).ofLp a' at h
        simpa only [hi] using h
      apply Fin.ext; exact congr_arg (Fin.val (n := q)) (ha' a' hv)
    let z := Points.cons 0 (Points.tail (Points.across (-(x 0)) x))
    let k := Fin.cons (α:=fun _ : Fin (n+1) => S.Tag) (⟨0,S.unit 0⟩) l
    let W := List.ofFn fun i=> ((z i,k i):Table.Species S)
    have hw : W=(0,⟨0,S.unit 0⟩)::classes S l (Points.tail (Points.across (-(x 0)) x)) := by
      dsimp only [W]; rw [List.ofFn_succ]; rfl
    intro a' i j h
    have hh := hgen (l':=k) (z:=z) he
    change positions S W ∈ generic _ at hh
    rw [hw] at hh; apply hh a'
    change positions _ ((0,_ ) :: _) i a' = positions _ ((0,_ ) :: _) j a'
    let A' := classes S l (Points.tail (Points.across (-(x 0)) x))
    have hEq (i : Fin (A'.length+1)) : positions _ ((0,(⟨0,S.unit 0⟩: S.Tag)) :: A') i a' = Points.cons 0 (positions _ A') i a' := by
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    convert! hEq i |>.trans (h.trans (hEq j).symm) using 1
  convert! (generic_across x (-(x 0))).mpr hx
  ext1 i; refine Fin.cases ?_ (fun _ => ?_) i
  · change 0=x 0+-x 0; exact (add_neg_cancel _).symm
  rfl

private lemma witnesses_nonnull (hs : S.Hierarchy) (d : ℕ) (q : S.Field d)
    (hb : ∀ E : ExteriorData S, Apt E → witnessAt S d E q=0) : q=0 := by
  apply S.faithfully; rw [map_zero]
  funext e; obtain ⟨n,x,l₀,hx⟩ := e
  let l := S.classTokens ∘ l₀
  rw [← Table.through S hs.laws.toSymmetric q l₀ hx]
  change S.useAt S x (Fin.cons ⟨d,q⟩ l) = 0
  let F x := S.useAt S (n:=n+1) x (Fin.cons ⟨d,q⟩ l)
  haveI : NeBot (𝓝[generic _] x) := mem_closure_iff_nhdsWithin_neBot.mp (Dash.full (n+1) x)
  exact tendsto_nhds_unique_of_eventuallyEq (f:=F)
    ((S.class_smooth S hs.smooth _).continuousOn.continuousAt ((conf_open _).mem_nhds hx)).continuousWithinAt.tendsto
    (tendsto_const_nhds (x:=(0:ℂ))) ((show ∀ᶠ y in 𝓝[generic _] x, y ∈ generic _ from self_mem_nhdsWithin).mono (fun y hy => show F y = 0 from by
      let v := Fin.cons (α:=fun _ : Fin (n+1) => S.Tag) ⟨d,q⟩ l
      let p := Points.across (-(y 0)) y
      calc
        F y = S.useAt S p v := (hs.translations _ _ (generic_conf _ hy) _ (fun i => detectorRaw S (v i))).symm
        _ = S.useAt S (Points.cons 0 (Points.tail p)) v := by
          congr; ext1 i; refine Fin.cases ?_ (fun _ => ?_) i <;> (first | solve | simp [Points.cons,p] | rfl)
        _ = _ := (witness_classes S q _ _).symm.trans (hb _ (classes_apt y hy l))))

/-- A finite readout list and exact left inverse on the unselected hierarchy.
The fixed lists can be included together with any additional probe demand;
they are not phase labels. -/
structure Detector (S : Table L) (d : ℕ) where
  size : ℕ
  listen : Fin size → ExteriorData S
  awake i : Apt (listen i)
  report : (Fin size → ℂ) →ₗ[ℂ] S.Field d
  recovered q : report (fun i => witnessAt S d (listen i) q) = q

lemma has_detectors (hs : S.Hierarchy) (d : ℕ) : Nonempty (Detector S d) := by
  let V := S.Field d
  let s := witnessAt (S:=S) S d '' {e | Apt e}
  let U := Submodule.span ℂ s
  obtain ⟨f,hf,hF,hZ⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ s
  choose E he hE using fun i=> hf i
  let M := LinearMap.pi f
  have hM : LinearMap.ker M=⊥ := LinearMap.ker_eq_bot'.mpr fun x hx => by
    have hV : x ∈ (Submodule.span ℂ (range f)).dualCoannihilator := by
      rw [(by rfl : (x∈_)= (x ∈ ((Submodule.span ℂ (range f)).dualCoannihilator : Set V))), Submodule.coe_dualCoannihilator_span]
      rintro _ ⟨i,rfl⟩; exact congr_fun hx i
    rw [hF] at hV
    exact witnesses_nonnull hs d x fun e he => Submodule.mem_dualCoannihilator _ |>.mp hV _ (Submodule.subset_span ⟨e,he,rfl⟩)
  obtain ⟨H,hH⟩ := M.exists_leftInverse_of_injective hM
  refine ⟨_,E,fun i=> he _,H,?_⟩
  intro q; change H (fun i => witnessAt (S:=S) S d (E i) q) = _; simp only [hE]; exact LinearMap.congr_fun hH q

end YM.OPE
