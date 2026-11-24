import YM.OPE.Compatible.Streams.Wipe
/-! # common paid portals.Cutting primitive shift etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts (d+1) μ v b (E i) G}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{p:Mints E}
variable (r t:ℕ→ℝ)
section
variable (J:∀ i,i<d+1→Eave L X T a (r i) (t i) u i)
noncomputable abbrev habitat (L:H→ℕ→L!) (r t:ℕ→ℝ) (d e:ℕ)(w:H):Submodule ℝ S! := Lingo (if e < d+1 then r e else t (e-1)) (L w)
include J
variable [∀ i,CompleteSpace (G i)]
lemma habitats (he:k < d+1)(x:H): habitat L r t d (k+1) x=Lingo (t k) (L x):=by
        unfold habitat; split
        next h=> exact ((J k he).Shade_eq _ _ _ (J k he).chip (J _ h).slope).symm
        next h=>rw [Nat.add_sub_cancel]
variable [∀ i,CompleteSpace (E i)][∀ i,FiniteDimensional ℝ (G i)]
noncomputable def Purs (x:H)(k:ℕ)(he:k < d+1): habitat L r t d k x→ₗ[ℝ] Fruition X (μ k):= (J k he|>.PO x).toLinearMap ∘ₗ Submodule.inclusion (le_of_eq (show habitat L r t d k x=Lingo (r k) _ from (by rw [habitat,if_pos he])))
lemma shapeP (x:H)(k:ℕ)(he:k<d+1)(p:habitat L r t d k x)(v:Lingo (r k) (L x))(hp:v.val=p.val): Purs r t J x k he p=(J k he).PO x v:=by
      unfold Purs; rw [LinearMap.comp_apply]; apply congr_arg ((J k he).PO x); apply Subtype.ext; exact hp.symm -- name
noncomputable def SwiftW: Aeon H T X a:=by
     let F:=habitat L r t d; have hp(i)(h:i<d+1)(x:H): F i x= Lingo (r i) (L x):=by unfold F habitat;rw[if_pos h]
     refine ⟨F,(fun k h i=>Purs r t J i k h),fun i=>?_,fun i w he=>?_,fun i x he p=>?_,fun i he w p z ht=>?_,fun i he=>?_,fun i=>(J 0 (Nat.zero_lt_succ _)).fits i⟩
     · rw [hp _ (Nat.zero_lt_succ _)]; exact top_unique fun z _=> Eave.wheel i (J _ (Nat.zero_lt_succ _)) _
     · rw [show F (i+1) w=_ from habitats r t J he w,hp _ he]; exact (J _ he).beside _
     · have h:p.val ∈ Lingo (r i) (L x):= by rw [← hp _ he]; exact p.property
       let y:Lingo (r i) (L x):=⟨_,h⟩; unfold F; rw [shapeP r t J x _ he p y rfl,habitats r t J he]; exact ((J _ he).fruitsZ x y).symm
     · have h:p.val∈ Lingo (r i) (L w):=by rw [←hp _ he]; exact p.property
       let U:= J i he; let y:Lingo (r i) (L w):=⟨_,h⟩; rw [shapeP r t J w _ he p y rfl]; exact ⟨U.lights w y z ht,U.herald w z.val z.isLt.le y ht,U.keeps w z y ht⟩ -- possible unfolds
     obtain ⟨a,b,k,H⟩:=(J _ he).OpFee; refine ⟨a,b,k,fun w p=>?_⟩; have h:p.val∈ Lingo (r i) (L w):=by rw[←hp _ he]; exact p.property
     rw [shapeP r t J w _ he p ⟨_,h⟩ rfl]; exact H w ⟨_,h⟩
end
end YM.OPE.Hark
