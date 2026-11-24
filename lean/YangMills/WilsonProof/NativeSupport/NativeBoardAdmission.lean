import YangMills.WilsonProof.NativeSupport.PhysicalScalarSector
import YM.FullVolume.Nectar.BerylN

/-! A fixed physical coefficient list is an admitted orchard on the entire
actual scalar sector. The common blank row exists on every board, even
when the vacuum activities on the unused part of the board vary. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.BoardAdmission
open RG Wilson Lattice Marker MergeProof PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Muse PhysicalNext.Repeat.Muse.Veil
open PhysicalNext.Repeat.Pass PhysicalNext.Repeat.Jams FullVolume.Ray FullVolume.Urns
open Extra.Iteration Progress.DirectedRecipe
open PhysicalNext.Repeat.Roof RG.Shoot AnalyticBridge VerifiedReset Collection
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {N m n : ℕ}
variable {T : Team (stageP R.alloy.B.a (m+1) n)}
local notation "Board₀" => Booker R.alloy N m n T
local notation "σ₀" => R.alloy.B.a.S.side (m+1) n
variable {V I : Type} [DecidableEq V] [Fintype I] {B : Census V}

theorem blank_everywhere (y : Board₀) (o : Site σ₀) (X : Support σ₀) (ho : o∈X) :
    (Lotus.Wing.logKey (Blush.found o X ho)).blank y.val.val.val := by
  exact y.val.property.regular _

theorem visit_iff_retained (C : Campaign R) (hm : m<N) (y : Board₀) :
    Orchard.Visit (C.L.prim N m n hm) y.val.val ↔
      R.alloy.B.bake.retain N (m+1) n y.val.val.val := by
  constructor
  · rintro ⟨_,_,_,S,t,_,_,ht⟩
    rw [ht]
    rcases (S.knows t t.property).1 with ⟨_,_,_,_,held⟩
    exact held
  intro held
  let X : ℝ → Rep G σ₀ := fun _ => y.val.val.val
  have waves : Curve (R.alloy.B.a.budget (m+1)) X (Set.Icc 0 0) := by
    rw [← y.val.val.property.1.point]
    exact Rain.unchanged ..
  have live : Lives R.alloy.B.bake N (m+1) n y.val.val.val := by
    rcases y.val.val.property.1 with ⟨p,e,c,l,_⟩
    exact ⟨p,e,c,l,held⟩
  obtain ⟨S,⟨ord,tone⟩,_⟩ := (C.L.prim N m n hm).spores 0 0 le_rfl X waves
    (fun _ _ => ⟨live,y.val.val.property.2⟩)
  exact ⟨0,0,X,S,⟨0,le_rfl,le_rfl⟩,tone,ord,rfl⟩

def move (x y : Board₀) (M : Lotus.Leaf x.val.val.val)
    (blank : M.turn.blank y.val.val.val) : Lotus.Leaf y.val.val.val where
  turn := M.turn
  ingredient := M.ingredient
  weight := M.weight
  earn := M.earn
  glows := M.glows
  borel := M.borel
  blank := blank
  grant U h := (ArmadaP.heart x y M.turn U) ▸ M.grant U h
  scopedR := by
    rw [← ArmadaP.touched x y,
      show y.val.val.val.p=x.val.val.val.p from
        y.val.val.property.1.point.trans x.val.val.property.1.point.symm]
    exact M.scopedR

def fixed (x : Board₀) (q : I→Menu.Hat B x.val.val.val)
    (slots : ∀ i (y : Board₀), (q i).M.turn.blank y.val.val.val) :
    Orchard (A:=R.alloy) N m n T B I ℝ where
  turn i := (q i).M.turn
  mode i := (q i).s
  va i := (q i).shiny
  charge i := (q i).charge
  orbit y _ i := move x y (q i).M (slots i y)
  serial _ _ _ := rfl
  color _ _ _ _ := rfl
  height _ _ _ _ := rfl

theorem admitted (x : Board₀) (q : I→Menu.Hat B x.val.val.val)
    (slots : ∀ i (y : Board₀), (q i).M.turn.blank y.val.val.val)
    (w : V→ℝ) (o : V→Site σ₀) (a : ℝ)
    (bill : Menu.Offer o q w (R.alloy.B.a.budget (m+1)).B
      ((R.alloy.B.a.budget (m+1)).supportExponent-4) a) :
    ∃ u, (fixed x q slots).Ensues w o a u := by
  let U := fixed x q slots
  have crest (y : Board₀) (s : ℝ) (i : I) :
      (U.orbit y s i).crest=(q i).M.crest :=
    (ArmadaP.touched x y (q i).M.turn).symm
  have loadEq (y : Board₀) (s : ℝ) (i : I) :
      load (U.orbit y s i)=load (q i).M := by
    unfold load
    rw [crest,show y.val.val.val.p = x.val.val.val.p from
      y.val.val.property.1.point.trans x.val.val.property.1.point.symm]
    rfl
  refine ⟨U.spend w x 0, ?_⟩
  constructor
  · exact ⟨fun _ _=>rfl,fun i F=>Nail.const ((q i).M.ingredient F)⟩
  · intro s y _
    refine ⟨fun i=> (crest y s i).symm ▸ bill.sites i,?_⟩
    have same : (fun i=>(U.hat y s i).M.crest) = (fun i=>(q i).M.crest) :=
      funext (crest y s)
    change Ac.Hit (fun i=>(U.hat y s i).M.crest) _ (fun i=>Menu.fare (q i) w) _ _
    rw [same]; exact bill.budget
  · intro y s v _
    change U.spend w y s v ≤ U.spend w x 0 v
    unfold Orchard.spend
    simp only [loadEq,le_refl]

end YM.Integration.InletSusceptibility.BoardAdmission
