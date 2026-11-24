import YM.Integration.WilsonPhysicalExteriorUVJoin

/-! The original all-arity Rake recursion on independently placed real
operators. A local cluster stays resolved on the true mesh while its exterior
can escape to infinity. Its signed fields and prescribed subtraction clock
are exactly the original ones. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorUVStory
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City Vane Land Menus
open scoped Topology ContDiff Classical
variable {I W : Type} {G : Gauge} {P : Geo I}

/-- A native lower spatial resolution for each genuine pair. There is no
upper bound on any individual, relative or common spatial translation. -/
def Resolved (P : Geo I) (x : Position W I) : Prop :=
  ∀ v w, v≠w → ∃ t:ℝ, 0<t ∧ ∀ i, P.roots i≤t*‖x v i-x w i‖

theorem constant_price {J : Type} {S : Scale J} {F : J→Law G} {u : J→ℝ}
    {b c : Bool} {C : ℝ} (hC : 0<C)
    (H : Lease b c S F (fun i=>u i*C)) : Lease b c S F u := by
  intro E _ _ w hw hr
  apply (H E w hw hr).raise
  refine ⟨C,hC,0,?_⟩
  intro i p hp
  change S.length i^pitch w*(u i*C) ≤ C*(S.full.cheap i p)^0*(S.length i^pitch w*u i)
  rw [pow_zero,mul_one]; exact le_of_eq (by ring)

variable [LinearOrder W] {x : Position W I} {s t : Finset W}

theorem split (hx : Resolved P x) (ht : t∈picks s) :
    ∃ T:ℝ, 0<T ∧ ∀ i, P.roots i ≤ T*‖(rootX x t-rootX x s) i‖ := by
  obtain ⟨_,ht₀,hst,_⟩ := n_small ht
  let c := s\t
  rw [unfT x ht,rootX,rootX,dif_pos ht₀,dif_pos hst]
  apply hx
  intro h
  exact (mem_sdiff.mp (min'_mem c hst)).2 (h ▸ min'_mem t ht₀)

variable {K L : Planet G I} {F : Site G I} {A : W→Site G I} {b : Bool}

private theorem joined {U V : Glade G I} {n m : ℕ} (h : Stage K L P b)
    (H : Resolved P x) (ht : t∈picks s) (hu : Tip P b false n U) (hv : Tip P b false m V) :
    Came P b (regionC (fun _=>planeF) (rootX x t-rootX x s) L U V) := by
  obtain ⟨T,hT,hR⟩ := split H ht
  refine ⟨⟨?_,warmJoin (fun _=>Coherent) h.pool hu.2.1 hv.2.1⟩,collect_join _ L hu.1 hv.1⟩
  intro k
  obtain ⟨q,hq⟩ := WilsonPhysicalExteriorUVJoin.early h hu hv (fun _=>T) (fun _=>hT.le) hR k
  exact constant_price (pow_pos hT q) hq

local notation "N" => story x (fun _=>planeF) K L F A

/-- Strong induction on the original set of marks and perturbation order of
the historical tree (Rake.Magic.stage), paying each real unfused split by
its own measured minimum separation. -/
theorem stage (h : Stage K L P b) (hx : Resolved P x)
    (hm : ∀ i : ℕ, 0 < i → Tip P b true 4 (F i))
    (ha : ∀ j k,∃ d,Tip P b false d (A j k)) (s : Finset W) (hs : s.Nonempty) (n : ℕ) :
    (∃ d,Tip P b false d (N s n)) ∧
      (2≤s.card → Came P b (N s n) ∧
        Trip (sailP (fun _=>planeF) L) (N s n) (multi (fun _=>planeF) x K L F (N s) N n s)) := by
  induction s using Finset.strongInductionOn generalizing n with
  | _ s ih =>
    by_cases hv : 2≤s.card
    · induction n using Nat.strong_induction_on with
      | h k hk =>
        let D := multi (fun _=>planeF) x K L F (N s) N k s
        have hD : Came P b D := by
          let Z := fun i : Finset W => rootX x i-rootX x s
          let Y := fun i : Finset W => ∑ j∈antidiagonal k,regionC (fun _=>planeF) (Z i) L
            (N i j.1) (N (s\i) j.2)
          let C := ∑ i∈picks s,Y i
          have hC : Came P b C := by
            refine seamount (fun i hi=>seamount (fun j _=>?_))
            obtain ⟨ht,hn,hr,hp⟩ := n_small hi
            obtain ⟨m,hm⟩ := (ih i ht hn j.1).1
            obtain ⟨d,hd⟩ := (ih (s\i) hp hr j.2).1
            exact joined h hx hi hm hd
          have hL : Came P b (lonely K F (N s) k) := by
            refine seamount (fun i hi=>?_); obtain hi' := Finset.mem_Ico.mp hi
            exact cone h ((hk _ hi'.2).2 hv).1 (hm _ (by omega))
          exact ⟨hL.1.add hC.1,collect_p hL.2 hC.2⟩
        have hS : Came P b (N s k) ∧ Trip (sailP (fun _=>planeF) L) (N s k) D :=
          st_n _ _ _ _ _ _ hv k ▸ wand_C h hD
        exact ⟨⟨0,Geo.tipby hS.1 0⟩,fun _=>hS⟩
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp
          (show s.card=1 from by obtain hpos := Finset.card_pos.mpr hs; omega)
      refine ⟨?_,fun p=>False.elim (hv p)⟩; rw [st_u]; exact ha i n

theorem fields (h : Stage K L P b) (hx : Resolved P x)
    (hm : ∀ i : ℕ, 0 < i → Tip P b true 4 (F i)) (ha : ∀ j k,∃ d,Tip P b false d (A j k)) :
    Fields x (fun _=>planeF) K L F A N ∧
      ∀ s : Finset W, 2≤s.card → ∀ n, Came P b (N s n) := by
  have hs (s:Finset W) (hp : 2≤s.card) (k : ℕ) :=
    (stage h hx hm ha s (Finset.card_pos.mp (by omega)) k).2 hp
  exact ⟨⟨st_0 x _ K L F A,st_u x _ K L F A,fun s hp k=>(hs s hp k).2⟩,
    fun s hp k=>(hs s hp k).1⟩

/-- Original dimensionally normalized subtraction data and the independent
original lattice marked fees both buy all signed orders, at the same
subtraction log and the same moving physical placement. -/
theorem installed {B : Local.Physical.Deck G} {O : Land.Booked B}
    (M : Land.MS_Data G O) (V : LitBook B) (T : Prescription B) (u : W→Label B)
    (hx : Resolved P x) :
    (let D:=constantP G I (PlanetD G)
     let A:=rowM P M ∘ u
     let E:=story x (fun _=>planeF) D D (approach P M) A
     Fields x (fun _=>planeF) D D (approach P M) A E ∧
       ∀ s : Finset W, 2≤s.card → ∀ n,Came P false (E s n)) ∧
    (let K:=constantP G I (LowP G)
     let L:=constantP G I (PlanetL G)
     let A:=rowK V P T ∘ u
     let E:=story x (fun _=>planeF) K L (initials P T) A
     Fields x (fun _=>planeF) K L (initials P T) A E ∧
       ∀ s : Finset W, 2≤s.card → ∀ n,Came P true (E s n)) :=
  ⟨fields (Geo.masterD ..) hx (fun _ _=>tagD P M _) (fun i k=>⟨_,tagF P M (u i) k⟩),
   fields (Geo.masterL ..) hx (fun _ _=>tagL P T _) (fun i k=>⟨_,tagX V P T (u i) k⟩)⟩

end YM.Integration.WilsonPhysicalExteriorUVStory
