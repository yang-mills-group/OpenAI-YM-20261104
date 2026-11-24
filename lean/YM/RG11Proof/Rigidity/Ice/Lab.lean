import YM.RG11Proof.Rigidity.Reads.Lit
import YM.RG11Proof.Rigidity.Ice.Glacier

/-!
# Presentation of all homogeneous real labels of the common free rooms.
Use different actual casts under the filtration-preserving pose (which
need no common basis beyond the specified horizon), then recognize only the total
top weight. Lift here before any interacting external coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD Reads Maxwell.Free Crowd
open scoped Classical BigOperators
variable {G : Gauge} {F : Frames G} {d e:ℕ}
abbrev grain {G : Gauge} (i : ℕ)(p:WickPol G) := MvPolynomial.IsWeightedHomogeneous scaleW p i
lemma web_grains (B:Adapted F d)(i:B.toBasis.J):grain (B.w i).1 (writes F d (B.b i)):=by
  intro p hp; have hi:= congrArg Prod.fst (B.alive i hp)
  -- first component of compile weight, scaleW=costKey. exact
  change Finsupp.weight scaleW p= _
  rw [show (scaleW:Slot G→ℕ) = costKey from rfl, ← hi,weight_collapse]

-- package each field AFTER choosing a direction. Stresses not realized at this stage.
lemma fits (x : E F d)(n : ℕ)(hv:x∈lower F n d)(hr:Basis.overReals x) :
    ∃ u : Cast G,canon u=writes F d x ∧ ∀ t∈u,ceilingG t.2≤ n := by
  let B := tower F d
  -- Each basis member has homogeneous real presentation.
  have hh (i:B.toBasis.J) := Reads.hom_present (B.w i).1 (p:=writes F d (B.b i))
    (show Extra.FD.barPol (writes F d (B.b i))=_ from by rw [← writes_bar F (table_spin F), B.pinned]) (web_grains B i)
  choose m hm hk using hh
  have he (s : Finset B.toBasis.J) : ∃ u : Cast G,canon u=∑ i∈s,B.b.equivFun x i • writes F d (B.b i) ∧
      ∀ t∈u,ceilingG t.2≤ n := by
    classical
    induction s using Finset.induction_on with
    | empty=> exact ⟨[],by simp [canon]⟩
    | insert a s ha ih=>
      obtain ⟨u,hu,ht⟩:=ih
      rw [Finset.sum_insert ha]
      rcases le_or_gt (B.w a).1 n with hy|hy; swap
      · rw [small_read B a hy _ hv,zero_smul,zero_add]; exact ⟨u,hu,ht⟩
      let z:= B.toBasis.coord x a
      let p := (m a).map (fun i=>(z*i.1,i.2))
      refine ⟨p ++ u,?_,fun t he=> ?_⟩
      · rw [canon_append,hu,show canon p=(z:ℂ) • canon (m a) from Reads.canon_scale _ _,hm]
        exact (B.toBasis.coord_real hr a) ▸ rfl
      rcases List.mem_append.mp he with he|he; swap; exact ht t he
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp he
      exact le_trans (hk a b hb).le hy
  obtain ⟨u,hu,hH⟩:=he Finset.univ
  refine ⟨u,?_,hH⟩
  rw [←B.b.sum_equivFun x,map_sum]; simp_rw [map_smul]; exact hu

/-- The cast meeting the declared engineering deadline. -/
def course (x:E F d){n}(hv:x∈ lower F n d)(hr:Basis.overReals x):=Classical.choose (fits x n hv hr)
lemma drawn (x:E F d){n}(hv:x∈ lower F n d)(hr:Basis.overReals x):
    canon (course x hv hr)=writes F d x ∧ ∀ a∈ course x hv hr,ceilingG a.2 ≤ n:= Classical.choose_spec (fits x n hv hr)

end YM.RG11.Rigidity.Ice
