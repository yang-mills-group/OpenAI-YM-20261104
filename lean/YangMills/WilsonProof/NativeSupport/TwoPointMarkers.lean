import YangMills.WilsonProof.NativeSupport.PaintedMarkers

/-! Two ordinary ring maps on the temporary colored census restore the
actual marked input at both real endpoints of a secant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.TwoPoint
open Finset Marker Extra.Trajectories Packet MarkerSubstitution Painted
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def letter (s : ℂ) (p : Ink V) : Poly (Stock.census V) :=
  Poly.send (tag {p.1}) (if p.2.2 then s else 1)

theorem square (s : ℂ) (p : Ink V) : letter s p * letter s p = 0 := by
  by_contra h
  obtain ⟨_,di,_⟩ := merges_of_tagged_mul h
  exact disjoint_left.mp di (mem_singleton_self p.1) (mem_singleton_self p.1)

def read (s : ℂ) := hom (letter (V:=V) s) (square s)

theorem restores (s : ℂ) (S : Finset V) (y : V) (hy : y∈S) (old tangent : Bool) (c : ℂ) :
    read s (Poly.send (tag (S.map (paint y old tangent))) c) =
      Poly.send (tag S) (c * (if tangent then s else 1)) := by
  let e := paint y old tangent
  let z (x : V) := tag ({x} : Finset V)
  let gain (x : V) : ℂ := if (e x).2.2 then s else 1
  have fit : Fits z S := by
    refine ⟨?_,mem_univ _⟩
    intro i _ j _ ne
    exact disjoint_singleton_left.mpr (fun h => ne (mem_singleton.mp h))
  have out : unionTag z S fit = tag S := by
    apply Subtype.ext
    change S.biUnion (fun i => {i})=S
    ext; simp
  have unit (i : V) (hi : i≠y) : gain i=1 := by simp [gain,e,paint,hi]
  have chosen : gain y=(if tangent then s else 1) := by simp [gain,e,paint]
  have cost : ∏ i∈S, gain i=(if tangent then s else 1) := by
    rw [prod_eq_single_of_mem y hy (fun _ _ hi=>unit _ hi),chosen]
  change applyTo (letter s) (Poly.send (tag (S.map e)) c)=_
  rw [on_send,prod_map]
  change c • (∏ i∈S,Poly.send (z i) (gain i))=_
  rw [tagged_prod z S fit,out,cost]
  ext k; rw [Poly.part_smul,Poly.part_send,Poly.part_send]; split <;> simp

theorem price {s : ℂ} (S : Finset (Ink V)) (w : V→ℝ) (A B : ℝ) (born : Finset V)
    (live : (∏ p∈S,letter s p)≠0) :
    (∏ p∈S,weight w A B born p) =
      (∏ x∈S.image Prod.fst,w x)*A^(S.filter (fun p=>p.2.1)).card*
        B^(S.filter (fun p=>p.1∈born)).card := by
  have fit := fits_of_tagged_prod (R:=Stock.census V)
    (fun p : Ink V=>tag ({p.1} : Finset V)) live
  have inj : Set.InjOn Prod.fst (S : Set (Ink V)) := by
    intro p hp q hq e
    by_contra ne
    exact disjoint_left.mp (fit.1 hp hq ne) (mem_singleton_self p.1) (mem_singleton.mpr e)
  have count (u : Ink V→Prop) [DecidablePred u] (v : ℝ) :
      (∏ p∈S, if u p then v else 1) = v^(S.filter u).card := by
    rw [← prod_filter,prod_const]
  simp only [weight,prod_mul_distrib,count]
  rw [prod_image (fun _ h₁ _ h₂ h=>inj h₁ h₂ h)]

end YM.Integration.InletSusceptibility.TwoPoint
