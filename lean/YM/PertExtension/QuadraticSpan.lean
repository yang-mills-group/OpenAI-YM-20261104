import YM.PertExtension.ReflectFrame
import YM.PertExtension.SignedPairs

/-! Quadratic curvature (weight four) Maxwell fields and exact symmetry of
their finite signed permutations. Includes link from the `Free` representation
to the actual comparison definition. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1800000
namespace YM.PertExtension.Quadratic
open Set Filter Function Tensor Analysis Labels Maxwell.Free Maxwell SignedPair Rigidity.Positive
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge}(F:Frames G) (H:(Model F).Hierarchy)
local notation "V" => YM.Table.Field (Model F) 4

def entryPol (e f:E) : WickPol G := team G (cell e.1 e.2) (cell f.1 f.2)
lemma entry_in (i j:E) : entryPol i j∈shellSector G 4 := team_label _ _ (by omega)
def entry (e f:E):V := (fields F 4).symm ⟨_,entry_in e f⟩
@[simp] lemma address_entry (e f:E) : address F 4 (entry F e f)=entryPol e f :=
    congr_arg Subtype.val ((fields F 4).apply_symm_apply _)

@[simp] lemma entry_real (e f:E) : (Model F).conj H.spin 4 (entry F e f)=entry F e f:= by
  apply address_inj F 4; simp only [address_star F,address_entry,entryPol,realTeam]

@[simp] lemma entry_swap1 (e f:E) : entry F (Prod.swap e) f= -entry F e f:= by
  apply address_inj F 4
  simp only [address_entry,map_neg,Prod.swap,entryPol]
  rw [show cell e.2 e.1=(-1:ℝ) • cell e.1 e.2 from (cell_skew e.2 e.1).trans (neg_one_smul ℝ (cell e.1 e.2)).symm,team_smul]
  simp

@[simp] lemma entry_swap2 (e f:E) : entry F e f.swap = -entry F e f:= by
  apply address_inj F 4; simp only [address_entry,map_neg,Prod.swap,entryPol]
  rw [team_swap G (cell e.1 e.2),team_swap G (cell e.1 e.2),show cell f.2 f.1=(-1:ℝ) • cell f.1 f.2 from (cell_skew f.2 f.1).trans (neg_one_smul ℝ (cell f.1 f.2)).symm,team_smul];simp

lemma entry_comm (e f:E) : entry F e f=entry F f e:=by
  apply address_inj F 4
  simp only [address_entry,entryPol]; exact team_swap ..

lemma entry_pushed (e f:E)(s:Equiv.Perm Axis) :
     (Model F).mirror H.spin 4 ⟨s,fun _=>false⟩ (entry F e f)=entry F (push s e) (push s f):=by
    apply address_inj F 4
    rw [address_motion F, address_entry,address_entry]
    simp only [entryPol,orient_team,tilt_one,push]; simp [tilt]

lemma entry_flip (e f:E) (a:Axis) :
    (Model F).mirror H.spin 4 (Signed.mirror a) (entry F e f) =
         ((sign a e.1*sign a e.2)*(sign a f.1*sign a f.2):ℝ) • entry F e f:=by
    apply address_inj F 4
    rw [address_motion F,address_entry, LinearMap.map_smul_of_tower,address_entry]
    unfold entryPol
    rw [orient_team,tilt_one,tilt_one]
    let q:=duetL G 0 0
    dsimp only [tilt,Signed.mirror]
    change q (_ • _) (_ • _) = _ • q _ _
    rw [map_smul (q (_ • _)), q.map_smul,LinearMap.smul_apply,smul_smul]
    congr 1
    simp only [decide_eq_true_eq,sign]
    ring

lemma entry_span (h:G.Simple) : (⊤:Submodule ℂ V) ≤ Submodule.span ℂ (Set.range (orbitAlt (entry F)) ∪ ({(Model F).unit 4})) := by
   let U := Submodule.span ℂ (Set.range (orbitAlt (entry F)) ∪ ({(Model F).unit 4}))
   let W := U.map (address F 4)
   have hm : Teams G 0 0 ≤ W := by
     let t:=duetL G 0 0
     let W₁:=W.restrictScalars ℝ
     have he (i j : E) (hi : i.1 < i.2) (hj : j.1 < j.2) : t (cell i.1 i.2) (cell j.1 j.2)∈W:= by
         obtain ⟨a,ha⟩:=enumerate _ _ hi; obtain ⟨b,hb⟩:=enumerate _ _ hj
         refine ⟨entry F i j,Submodule.subset_span (Or.inl ⟨(a,b),?_⟩),address_entry F ..⟩
         unfold orbitAlt;dsimp only; rw [ha,hb]
     let w := {x:Flavor 0|∃ a b:Axis,a<b ∧ x=cell a b}
     have ht (i:Flavor 0) (hi:i∈w) : ⊤ ≤ W₁.comap (t i):= Eq.symm cell_span ▸ (Submodule.span_le.mpr (show w⊆ (W₁.comap (t i)) by 
         obtain ⟨a,b,hh,rfl⟩:=hi; rintro x ⟨u,v,h,rfl⟩; exact he (a,b) (u,v) hh h))
     have hu (j:Flavor 0): ⊤ ≤ W₁.comap (t.flip j):= by
       have he : (⊤ : Submodule ℝ (Flavor 0)) = Submodule.span ℝ w:=cell_span.symm
       rw [he,Submodule.span_le]
       rintro u hv
       have hh := ht u hv (show j ∈ (⊤:Submodule ℝ (Flavor 0)) from Submodule.mem_top)
       change t u j∈W₁; change t u j∈W₁ at hh; exact hh
     rw [Teams,Submodule.span_le]; rintro x ⟨u,v,rfl⟩
     change u∈W₁.comap (t.flip v)
     exact hu v (Submodule.mem_top (x:=u))
   have hUnit : BottomOnly G ≤ W:= by
     rw [BottomOnly,Submodule.span_le];rintro p hp; change p∈W
     obtain rfl:p=(1:WickPol G):=hp
     exact ⟨(Model F).unit 4,Submodule.subset_span (Or.inr rfl),unit_address ..⟩
   intro p hp
   obtain ⟨q,hq,he⟩:= (sup_le hUnit hm) ((low_support h) ▸ address_in F 4 p)
   exact address_inj F 4 he ▸ hq

def realField (d:ℕ) : Submodule ℝ ((Model F).Field d) := by
   exact {
   carrier:={x|(Model F).conj H.spin d x=x}
   zero_mem':=map_zero _
   add_mem':=fun hx hy=>by simp only [Set.mem_setOf_eq] at *;rw [map_add,hx,hy]
   smul_mem':=fun {t x} hx=>by
      change (Model F).conj H.spin d _=_
      change (Model F).conj H.spin d _=_ at hx
      simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smulₛₗ, hx]
      simp
   }

def realEntry (e f:E) : realField F H 4 := ⟨entry F e f,entry_real F H e f⟩

def coefficients (x : V) : Prop := (Model F).conj H.spin 4 x=x

lemma into_real {X : Set V} (hr:∀ x∈X,(Model F).conj H.spin 4 x=x)(x:V)
    (he:x∈Submodule.span ℂ X)(h: (Model F).conj H.spin 4 x=x): x∈Submodule.span ℝ X := by
  let K := Submodule.span ℝ X
  let A := (1/2:ℝ)
  let c := (Model F).conj H.spin 4
  suffices ht : ∀ q∈Submodule.span ℂ X,∀ z : ℂ,z • q+c (z • q) ∈ K by
    have hv := ht x he (A:ℂ)
    rw [map_smulₛₗ, show c x=x from h,Complex.conj_ofReal,
       ← add_smul,show (A:ℂ)+(A:ℂ)=1 by unfold A;push_cast; norm_num,one_smul] at hv
    exact hv
  intro q h; induction h using Submodule.span_induction with
  | mem u h =>
    intro k; unfold c at *
    rw [map_smulₛₗ,hr u h, ← add_smul, show k+(starRingEnd ℂ) k=((↑(2*k.re):ℂ)) from ?_]
    change ((↑(2*k.re):ℂ) • u∈ _)
    exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ u) ▸ Submodule.smul_mem _ _ (Submodule.subset_span h)
    apply Complex.ext <;> (simp; first | done | ring)
  | zero => simp [K]
  | add x y _ _ h v =>
    intro z; rw [smul_add,map_add,add_add_add_comm]; exact Submodule.add_mem K (h z) (v z)
  | smul t p _ h => intro z; rw [smul_smul]; exact h _

def one : realField F H 4 := ⟨(Model F).unit 4, Table.conj_unit ..⟩
lemma occupy (hg:G.Simple) :
   (⊤:Submodule ℝ (realField F H 4)) ≤ Submodule.span ℝ (Set.range (orbitAlt (realEntry F H)) ∪ ({one F H})) := by
   let W:=Submodule.span ℝ (Set.range (orbitAlt (realEntry F H)) ∪ ({one F H}))
   let z:=Set.range (orbitAlt (entry F)) ∪ ({(Model F).unit 4})
   let P:=(realField F H 4).subtype
   have he:(⊤: Submodule ℝ (realField F H 4)) ≤ (Submodule.span ℝ z).comap P := by
      intro x hx
      exact into_real F H (by
          rintro x (⟨i,rfl⟩|h)
          · exact entry_real F H ..
          obtain rfl :x=(Model F).unit 4:=h; simp) _ ((entry_span F hg) (Submodule.mem_top)) x.property
   have ht : Submodule.span ℝ z ≤ W.map P := by
      apply Submodule.span_le.mpr; rintro x (⟨v,rfl⟩| h)
      · exact ⟨orbitAlt (realEntry F H) v, Submodule.subset_span (Or.inl (Set.mem_range_self v)),rfl⟩
      obtain rfl :x=(Model F).unit 4:=h
      exact ⟨one F H,Submodule.subset_span (Or.inr (Set.mem_singleton _)),rfl⟩
   exact he.trans <| (Submodule.comap_mono ht).trans (le_of_eq (Submodule.comap_map_eq_of_injective (show Injective P from Subtype.val_injective) W))

end YM.PertExtension.Quadratic
