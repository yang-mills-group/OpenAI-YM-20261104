import YM.OPE.Compatible.Cant.Knit
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {i j m:ℕ}{μ:ℝ}{U:Jewel E→ₗ[ℝ] Jewel E}{V:ℕ→ ΦB E}
noncomputable abbrev τ₀ (E:Type)[AddCommGroup E][Module ℝ E]:E→ₗ[ℝ] Jewel E:=LinearMap.single ℝ (fun _:Fin 3=> E) 0
lemma τat (x:E): τ₀ E x 0=x:= by simp [τ₀]
lemma τnext (x:Jewel E):∃ y:Jewel E,x=τ₀ E (x 0)+τΓ E y:=by
      use τ₀ E (x 1)+ τΓ E (τ₀ E (x 2))
      rw [map_add,← add_assoc]; exact (τwrite x).symm
lemma Metricζ (f:Artπ (Jewel E)) (h:∀ x y, f (τΓ E x) y=0∧ f x (τΓ E y)=0) (x y:Jewel E): f x y=f (τ₀ E (x 0)) (τ₀ E (y 0)):=by
       let a:=f (τ₀ E (x 0)); obtain ⟨p,hp⟩:= τnext x; obtain ⟨q,hq⟩:= τnext y; calc
          _=f (τ₀ E (x 0)+τΓ E p) (τ₀ E (y 0)+τΓ E q):= by rw [← hp,← hq];
          _ = _ := by simp only [map_add,LinearMap.add_apply,(h ..).1,(h ..).2,add_zero]
variable (H:Svet V U μ)
noncomputable abbrev partPay :Artπ (Jewel E) := ((V 0 2).comp U).compl₂ U- (μ*μ) • (V 0 2)
lemma partEq (x y:Jewel E):partPay (V:=V) (U:=U) (μ:=μ) x y=V 0 2 (U x) (U y)-(μ*μ)*V 0 2 x y:= rfl
include H
lemma lowerPQ (x y:Jewel E): V (m+1) 2 x y=V m 2 (U x) (U y):= H.fuel m 2 _ _
lemma partPay' (x y:Jewel E): partPay (V:=V) (U:=U) (μ:=μ) x y=partPay (V:=V) (U:=U) (μ:=μ) (τ₀ E (x 0)) (τ₀ E (y 0)):=by
       apply Metricζ (partPay (μ:=μ)) _ x y; intro x y; rw [partEq,partEq]; rw [H.slip x,H.slip y,(H.drum.two ..).1,(H.drum.two ..).1,(H.drum.two ..).2,(H.drum.two ..).2,H.winds]; rw [sub_self]; exact ⟨rfl,rfl⟩
lemma partRide (x y:Jewel E): partPay (V:=V) (U:=U) (μ:=μ) (U x) (U y)= μ^2*partPay (V:=V) (U:=U) (μ:=μ) x y:=by rw [partPay' H, H.capT x,H.capT y,map_smul,map_smul,map_smul, LinearMap.smul_apply,map_smul,partPay' H x y]; simp only [smul_eq_mul]; ring
lemma bubbleC (x y:Jewel E)(hp:μ≠0) (i:ℕ): V i 2 x y=(μ^i)^2 * (V 0 2 x y+(i:ℝ)/(μ^2)*partPay (V:=V) (U:=U) (μ:=μ) x y):=by
       induction i generalizing x y with
       | zero=> simp
       | succ i ih=> rw[H.fuel,ih,partRide H,partEq]; push_cast; field_simp [hp]; ring
lemma chargeOne (x y:Jewel E)(i:ℕ): V i 1 x y=(μ^i)^2* V 0 1 x y:=by induction i generalizing x y with| zero=>simp| succ i ih=>rw[H.fuel,ih,H.winds,pow_succ]; ring
end YM.OPE.Hark
